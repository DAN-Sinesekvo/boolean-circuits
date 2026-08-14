/* ============================================================
   GATE MODE + CIRCUIT GRAPH BUILDING
   Every mode is restricted to 2-input gates. We build an abstract
   AND/OR/XOR/VAR expression tree from the minimized SOP (or POS,
   for the NOR case), then "materialize" it into a DAG of concrete
   2-input gate nodes, choosing (per mode) which gate family is
   allowed and reusing one shared inverter per complemented
   variable rather than duplicating inverters at every use site.
============================================================ */

// POS "sum" factor: `lits` represent the AND-term of F' (from Quine-McCluskey on the
// 0s); by De Morgan the matching POS factor is the OR of the *complemented* literals.
function posFactorLiterals(lits){
  return lits.map(l=>({name:l.name, comp: !l.comp}));
}

// Detect pairs of 2-literal SOP terms over the same two variables that combine into a
// single XOR or XNOR gate (X'Y+XY' = X^Y ; XY+X'Y' = X⊙Y), for the "Simplified" mode.
function findXorPairs(terms){
  const used = new Set();
  const compounds = [];
  for(let i=0;i<terms.length;i++){
    if(used.has(i) || terms[i].length!==2) continue;
    for(let j=i+1;j<terms.length;j++){
      if(used.has(j) || terms[j].length!==2) continue;
      const a=terms[i], b=terms[j];
      const namesA=a.map(l=>l.name).sort().join(','), namesB=b.map(l=>l.name).sort().join(',');
      if(namesA!==namesB) continue;
      const aMap={}; a.forEach(l=>aMap[l.name]=l.comp);
      const bMap={}; b.forEach(l=>bMap[l.name]=l.comp);
      const names=a.map(l=>l.name); const n1=names[0], n2=names[1];
      const aPat=[aMap[n1],aMap[n2]], bPat=[bMap[n1],bMap[n2]];
      const isXor  = (aPat[0]!==aPat[1]) && (bPat[0]!==bPat[1]) && (aPat[0]!==bPat[0]);
      const isXnor = (aPat[0]===aPat[1]) && (bPat[0]===bPat[1]) && (aPat[0]!==bPat[0]);
      if(isXor || isXnor){
        used.add(i); used.add(j);
        compounds.push({type: isXor?'XOR':'XNOR', vars:[n1,n2]});
        break;
      }
    }
  }
  return {compounds, used};
}

// Builds a full node graph {nodes, outputId, constMsg} for the given mode ('simplified',
// 'basic', 'nand', 'nor'). nodes: array of {id, kind:'INPUT'|'GATE'|'OUTPUT'|'DUMMY',
// gateType, label, inputs:[nodeId,...]}. Nodes are always pushed in dependency order
// (a node's inputs are always created before the node itself).
function buildCircuitGraph(mode){
  const nodes = [];
  let idCounter = 0;
  const newId = ()=>'g'+(idCounter++);
  const varInputCache = {};
  const invCache = {};

  // Tracks each node's logic-depth (longest path from a primary input, in gate hops) as
  // nodes are created, so the tree-building helpers below can balance by *arrival time*
  // rather than by list position — this is what keeps e.g. "A+B+C.D" at 2 levels instead
  // of accidentally chaining a fresh 2-input OR onto an already-deep subtree.
  const depthOf = {};
  function addNode(props){
    const n=Object.assign({id:newId(), inputs:[]}, props);
    nodes.push(n);
    n.depth = (n.kind==='GATE' && n.inputs.length)
      ? Math.max(...n.inputs.map(id=>depthOf[id]||0)) + 1
      : 0;
    depthOf[n.id]=n.depth;
    return n;
  }
  function getVarInput(name){
    if(varInputCache[name]) return varInputCache[name];
    const n = addNode({kind:'INPUT', label:name, order:varNames.indexOf(name)});
    varInputCache[name]=n; return n;
  }
  // One shared inverter per (variable, gate-family) — reused by every consumer that needs
  // that variable's complement, instead of a fresh inverter per occurrence.
  function getSharedInverter(name, gt){
    const key=name+'|'+gt;
    if(invCache[key]) return invCache[key];
    const src=getVarInput(name);
    const n = (gt==='NOT')
      ? addNode({kind:'GATE', gateType:'NOT', inputs:[src.id]})
      : addNode({kind:'GATE', gateType:gt, inputs:[src.id, src.id]}); // tied-input NAND/NOR = inverter
    invCache[key]=n; return n;
  }
  function literalId(lit, invType){
    const inp = getVarInput(lit.name);
    return lit.comp ? getSharedInverter(lit.name, invType).id : inp.id;
  }
  // Combine a flat list of node-ids into a minimum-depth binary tree of 2-input `op`
  // gates. Items being combined can already sit at different depths (e.g. when OR-ing
  // together a bare literal — depth 0 — with a product term that needed its own AND
  // gate — depth 1), so a plain "pair up by list position" balancer can needlessly
  // chain a shallow item onto a deep one and add an extra level. Instead this always
  // merges the two currently-shallowest items first (a small min-heap via sort, fine
  // at classroom scale): every merge costs max(depthA,depthB)+1, so resolving the
  // shallow items amongst themselves first keeps that max — and the final depth —
  // as low as possible. This greedy shallowest-first merge is optimal for minimizing
  // the resulting tree's depth.
  function buildBalanced(items, op){
    if(items.length===0) return null;
    let queue = items.map(id=>({id, depth: depthOf[id]||0}));
    while(queue.length>1){
      queue.sort((a,b)=>a.depth-b.depth);
      const a=queue.shift(), b=queue.shift();
      const g = addNode({kind:'GATE', gateType:op, inputs:[a.id,b.id]});
      queue.push({id:g.id, depth:g.depth});
    }
    return queue[0].id;
  }
  // Same shallowest-first idea, but over abstract (not-yet-materialized) tree nodes —
  // used for NAND/NOR modes, where depth is the structural op-tree depth rather than a
  // realized gate count (they track closely once materialized).
  function buildBalancedAbstract(items, op){
    if(items.length===1) return items[0];
    let queue = items.map(n=>({node:n, depth:n.depth||0}));
    while(queue.length>1){
      queue.sort((a,b)=>a.depth-b.depth);
      const a=queue.shift(), b=queue.shift();
      const depth = Math.max(a.depth,b.depth)+1;
      queue.push({node:{op, a:a.node, b:b.node, depth}, depth});
    }
    return queue[0].node;
  }
  function buildExprTree(terms, innerOp, outerOp){
    const termTrees = terms.map(t=>buildBalancedAbstract(t.map(l=>({op:'VAR', name:l.name, comp:l.comp, depth:0})), innerOp));
    return buildBalancedAbstract(termTrees, outerOp);
  }

  // Converts an AND/OR/VAR tree into 2-input NAND gates only, via De Morgan bubble-
  // pushing. wantComp requests the node's true value (false) or complement (true).
  function materializeNand(node, wantComp){
    if(node.op==='VAR'){
      const rawId = getVarInput(node.name).id;
      const finalComp = wantComp ? !node.comp : node.comp;
      return finalComp ? getSharedInverter(node.name,'NAND').id : rawId;
    }
    if(node.op==='AND'){
      const na=materializeNand(node.a,false), nb=materializeNand(node.b,false);
      const g1=addNode({kind:'GATE', gateType:'NAND', inputs:[na,nb]}).id; // = complement of AND
      if(wantComp) return g1;
      return addNode({kind:'GATE', gateType:'NAND', inputs:[g1,g1]}).id; // invert to get true AND
    } else { // OR
      const na=materializeNand(node.a,true), nb=materializeNand(node.b,true);
      const g1=addNode({kind:'GATE', gateType:'NAND', inputs:[na,nb]}).id; // = true OR (De Morgan)
      if(!wantComp) return g1;
      return addNode({kind:'GATE', gateType:'NAND', inputs:[g1,g1]}).id; // invert to get NOR
    }
  }
  // Symmetric construction for NOR-only, built from an OR/AND/VAR (POS) tree.
  function materializeNor(node, wantComp){
    if(node.op==='VAR'){
      const rawId = getVarInput(node.name).id;
      const finalComp = wantComp ? !node.comp : node.comp;
      return finalComp ? getSharedInverter(node.name,'NOR').id : rawId;
    }
    if(node.op==='OR'){
      const na=materializeNor(node.a,false), nb=materializeNor(node.b,false);
      const g1=addNode({kind:'GATE', gateType:'NOR', inputs:[na,nb]}).id; // = complement of OR
      if(wantComp) return g1;
      return addNode({kind:'GATE', gateType:'NOR', inputs:[g1,g1]}).id;
    } else { // AND
      const na=materializeNor(node.a,true), nb=materializeNor(node.b,true);
      const g1=addNode({kind:'GATE', gateType:'NOR', inputs:[na,nb]}).id; // = true AND (De Morgan)
      if(!wantComp) return g1;
      return addNode({kind:'GATE', gateType:'NOR', inputs:[g1,g1]}).id;
    }
  }

  const sopTerms = lastResult.sopTerms;
  const posFactors = lastResult.posTerms.map(posFactorLiterals);
  const sopIsConst0 = sopTerms.length===0;
  const sopIsConst1 = sopTerms.length===1 && sopTerms[0].length===0;
  const posIsConst1 = posFactors.length===0;
  const posIsConst0 = posFactors.length===1 && posFactors[0].length===0;

  let rootId=null, constMsg=null;

  if(mode==='basic' || mode==='simplified'){
    if(sopIsConst0) constMsg = 'The output is always 0, so no gates are needed.';
    else if(sopIsConst1) constMsg = 'The output is always 1, so no gates are needed.';
    else {
      let termIds;
      if(mode==='simplified'){
        const {compounds, used} = findXorPairs(sopTerms);
        const compoundIds = compounds.map(c=>{
          const aId=getVarInput(c.vars[0]).id, bId=getVarInput(c.vars[1]).id;
          const xg = addNode({kind:'GATE', gateType:'XOR', inputs:[aId,bId]}).id;
          return c.type==='XNOR' ? addNode({kind:'GATE', gateType:'NOT', inputs:[xg]}).id : xg;
        });
        const restIds = sopTerms.map((t,i)=> used.has(i) ? null : buildBalanced(t.map(l=>literalId(l,'NOT')), 'AND'))
                                 .filter(x=>x!==null);
        termIds = compoundIds.concat(restIds);
      } else {
        termIds = sopTerms.map(t=>buildBalanced(t.map(l=>literalId(l,'NOT')), 'AND'));
      }
      rootId = buildBalanced(termIds, 'OR');
    }
  } else if(mode==='nand'){
    if(sopIsConst0) constMsg = 'The output is always 0, so no gates are needed.';
    else if(sopIsConst1) constMsg = 'The output is always 1, so no gates are needed.';
    else rootId = materializeNand(buildExprTree(sopTerms, 'AND', 'OR'), false);
  } else if(mode==='nor'){
    if(posIsConst1) constMsg = 'The output is always 1, so no gates are needed.';
    else if(posIsConst0) constMsg = 'The output is always 0, so no gates are needed.';
    else rootId = materializeNor(buildExprTree(posFactors, 'OR', 'AND'), false);
  }

  let outputId=null;
  if(rootId){ outputId = addNode({kind:'OUTPUT', inputs:[rootId]}).id; }
  return {nodes, outputId, constMsg};
}

/* ============================================================
   LAYERED LAYOUT (Sugiyama-style): longest-path layering, dummy
   nodes for edges spanning multiple layers, barycenter ordering
   to reduce crossings, then coordinate assignment.
============================================================ */
function computeLayers(nodes){
  const map = new Map();
  nodes.forEach(n=>{
    if(n.kind==='INPUT'){ n.layer=0; }
    else {
      let l=0;
      (n.inputs||[]).forEach(iid=>{ l=Math.max(l, map.get(iid).layer+1); });
      n.layer=l;
    }
    map.set(n.id,n);
  });
}

function expandLongEdges(nodes){
  const map = new Map(nodes.map(n=>[n.id,n]));
  let dc=0;
  nodes.slice().forEach(n=>{
    if(!n.inputs || n.inputs.length===0) return;
    n.inputs = n.inputs.map(srcId=>{
      let cur = map.get(srcId);
      while(n.layer - cur.layer > 1){
        const d = {id:'dum'+(dc++), kind:'DUMMY', inputs:[cur.id], layer:cur.layer+1};
        nodes.push(d); map.set(d.id,d);
        cur = d;
      }
      return cur.id;
    });
  });
}

function orderLayers(nodes){
  const byLayer={};
  nodes.forEach(n=>{ (byLayer[n.layer]=byLayer[n.layer]||[]).push(n); });
  Object.values(byLayer).forEach(arr=>arr.forEach((n,i)=>{ if(n.order===undefined) n.order=i; }));
  const map = new Map(nodes.map(n=>[n.id,n]));
  const consumers = new Map();
  nodes.forEach(n=>{ (n.inputs||[]).forEach(iid=>{ if(!consumers.has(iid)) consumers.set(iid,[]); consumers.get(iid).push(n.id); }); });
  const layerKeys = Object.keys(byLayer).map(Number).sort((a,b)=>a-b);
  for(let pass=0; pass<4; pass++){
    const forward = pass%2===0;
    const order = forward ? layerKeys : layerKeys.slice().reverse();
    order.forEach(L=>{
      const arr = byLayer[L];
      arr.forEach(n=>{
        let refs = forward ? (n.inputs||[]).map(iid=>map.get(iid).order)
                            : (consumers.get(n.id)||[]).map(cid=>map.get(cid).order);
        n._bary = refs.length ? refs.reduce((a,b)=>a+b,0)/refs.length : n.order;
      });
      arr.sort((a,b)=>a._bary-b._bary);
      arr.forEach((n,i)=>n.order=i);
    });
  }
}

const CIRC = {colWidth:160, rowHeight:70, marginX:90, marginY:40, GW:64, GH:36, NW:42, NH:26, BR:4.5};

function assignCoords(nodes){
  const byLayer={};
  nodes.forEach(n=>{ (byLayer[n.layer]=byLayer[n.layer]||[]).push(n); });
  Object.entries(byLayer).forEach(([L,arr])=>{
    arr.sort((a,b)=>a.order-b.order);
    arr.forEach((n,i)=>{ n.x = CIRC.marginX + Number(L)*CIRC.colWidth; n.y = CIRC.marginY + i*CIRC.rowHeight; });
  });
}

// Nudge each node toward the average y of its inputs (keeping order & minimum spacing)
// so straight-through connections stay straight instead of zig-zagging needlessly.
function refineY(nodes){
  const map = new Map(nodes.map(n=>[n.id,n]));
  const maxLayer = Math.max(...nodes.map(n=>n.layer));
  for(let L=1; L<=maxLayer; L++){
    const arr = nodes.filter(n=>n.layer===L).sort((a,b)=>a.order-b.order);
    arr.forEach(n=>{
      const refs = (n.inputs||[]).map(iid=>map.get(iid).y);
      n._desired = refs.length ? refs.reduce((a,b)=>a+b,0)/refs.length : n.y;
    });
    for(let i=0;i<arr.length;i++){
      let y = arr[i]._desired;
      if(i>0) y = Math.max(y, arr[i-1].y + CIRC.rowHeight);
      arr[i].y = y;
    }
  }
}

/* ============================================================
   SVG RENDERING — gate shapes, routed orthogonal wires, and
   small "hop" jumps where unrelated wires cross.
============================================================ */
function gateHasBubble(gt){ return gt==='NAND'||gt==='NOR'||gt==='NOT'; }

function outPoint(n){
  const {GW,NW,BR} = CIRC;
  if(n.kind==='INPUT'||n.kind==='DUMMY') return {x:n.x, y:n.y};
  if(n.kind==='GATE'){
    // Wire starts at the gate body's tip, or the bubble's far edge if it has one —
    // never a floating gap.
    const tip = n.x + (n.gateType==='NOT' ? NW : GW);
    return {x: tip + (gateHasBubble(n.gateType) ? 2*BR : 0), y:n.y};
  }
  return {x:n.x, y:n.y};
}
function inPoints(n){
  const {GW,GH} = CIRC;
  if(n.kind==='INPUT') return [];
  if(n.kind==='DUMMY' || n.kind==='OUTPUT') return [{x:n.x, y:n.y}];
  if(n.gateType==='NOT') return [{x:n.x, y:n.y}];
  const top = n.y - GH/2;
  return [{x:n.x, y:top+GH*0.26}, {x:n.x, y:top+GH*0.74}];
}

function drawGateNode(n){
  const {GW,GH,NW,NH,BR} = CIRC;
  if(n.gateType==='NOT'){
    const x=n.x, y=n.y-NH/2, w=NW, h=NH;
    // Bubble is tangent to the triangle's apex (at x+w), so there's no gap between them.
    let out = `<path d="M ${x} ${y} L ${x+w} ${y+h/2} L ${x} ${y+h} Z" fill="#1e293b" stroke="#38bdf8" stroke-width="2"/>`;
    out += `<circle cx="${x+w+BR}" cy="${y+h/2}" r="${BR}" fill="#0b1220" stroke="#38bdf8" stroke-width="2"/>`;
    return out;
  }
  const x=n.x, y=n.y-GH/2, w=GW, h=GH, r=h/2;
  const isAndFamily = n.gateType==='AND'||n.gateType==='NAND';
  let d;
  if(isAndFamily){
    // Flat sides run to (w - r), then a semicircular bulge carries the curve to x+w,
    // matching every other gate family's tip (see outPoint()).
    const flat = w - r;
    d = `M ${x} ${y} h ${flat} a ${r} ${r} 0 0 1 0 ${h} h ${-flat} Z`;
  } else {
    // OR/XOR/NOR: convex front curving to a point at exactly x+w, concave notch at back.
    d = `M ${x} ${y} Q ${x+w*0.55} ${y} ${x+w} ${y+h/2} Q ${x+w*0.55} ${y+h} ${x} ${y+h} Q ${x+w*0.2} ${y+h/2} ${x} ${y} Z`;
  }
  let out = `<path d="${d}" fill="#1e293b" stroke="#38bdf8" stroke-width="2"/>`;
  if(n.gateType==='XOR'){
    out += `<path d="M ${x-6} ${y} q ${w*0.2} ${h/2} 0 ${h}" fill="none" stroke="#38bdf8" stroke-width="2"/>`;
  }
  out += `<text x="${x+w*0.16}" y="${n.y+4}" fill="#e2e8f0" font-size="10.5" font-weight="700">${n.gateType}</text>`;
  if(gateHasBubble(n.gateType)){
    // Same tangent-bubble treatment as NOT (see above).
    out += `<circle cx="${x+w+BR}" cy="${n.y}" r="${BR}" fill="#0b1220" stroke="#38bdf8" stroke-width="2"/>`;
  }
  return out;
}

function renderCircuitSVG(nodes, outputId){
  const map = new Map(nodes.map(n=>[n.id,n]));

  // One wire per input pin: a straight line if source/dest share a y, else a
  // 3-segment orthogonal Z-route.
  let wireId=0;
  const wires=[];
  nodes.forEach(n=>{
    if(!n.inputs) return;
    const pins = inPoints(n);
    n.inputs.forEach((srcId, idx)=>{
      const src = map.get(srcId);
      const sp = outPoint(src);
      const dp = pins[idx] || pins[0];
      const straight = Math.abs(sp.y-dp.y) < 0.5;
      const pts = straight
        ? [[sp.x,sp.y],[dp.x,sp.y]]
        : [[sp.x,sp.y],[(sp.x+dp.x)/2,sp.y],[(sp.x+dp.x)/2,dp.y],[dp.x,dp.y]];
      wires.push({id:'w'+(wireId++), points:pts, srcLayer:src.layer});
    });
  });

  // Spread parallel wires' vertical bends across the column gap so they don't overlap.
  const groups={};
  wires.forEach(w=>{ (groups[w.srcLayer]=groups[w.srcLayer]||[]).push(w); });
  Object.values(groups).forEach(g=>{
    const bendWires = g.filter(w=>w.points.length===4);
    if(bendWires.length<=1) return;
    bendWires.sort((a,b)=>(a.points[0][1]+a.points[3][1])-(b.points[0][1]+b.points[3][1]));
    const gapStart = Math.min(...bendWires.map(w=>w.points[0][0]));
    const gapEnd = Math.max(...bendWires.map(w=>w.points[3][0]));
    const n = bendWires.length;
    bendWires.forEach((w,i)=>{
      const bx = gapStart + (i+1)/(n+1)*(gapEnd-gapStart);
      w.points[1][0]=bx; w.points[2][0]=bx;
    });
  });

  // Flatten into H/V segments (tagged by wire) for crossing detection.
  const segs=[];
  wires.forEach(w=>{
    for(let i=0;i<w.points.length-1;i++){
      const [x1,y1]=w.points[i], [x2,y2]=w.points[i+1];
      if(y1===y2) segs.push({type:'H', wireId:w.id, y:y1, x1:Math.min(x1,x2), x2:Math.max(x1,x2)});
      else segs.push({type:'V', wireId:w.id, x:x1, y1:Math.min(y1,y2), y2:Math.max(y1,y2)});
    }
  });

  // Renders one wire's path, adding a small bump where it crosses another wire's
  // vertical run (standard schematic "jump" convention for unconnected wires).
  function pathForWire(w){
    let d='';
    for(let i=0;i<w.points.length-1;i++){
      const [x1,y1]=w.points[i], [x2,y2]=w.points[i+1];
      if(d==='') d += `M ${x1} ${y1} `;
      if(y1===y2){
        const xa=Math.min(x1,x2), xb=Math.max(x1,x2);
        const crosses=[];
        segs.forEach(s=>{
          if(s.wireId===w.id || s.type!=='V') return;
          if(s.x>xa+3 && s.x<xb-3 && y1>s.y1+3 && y1<s.y2-3) crosses.push(s.x);
        });
        const dir = x1<x2 ? 1 : -1;
        crosses.sort((p,q)=> dir>0 ? p-q : q-p);
        const hopR=6;
        crosses.forEach(cx=>{
          const before=cx-dir*hopR, after=cx+dir*hopR;
          d += `L ${before} ${y1} Q ${cx} ${y1-9} ${after} ${y1} `;
        });
        d += `L ${x2} ${y2} `;
      } else {
        d += `L ${x2} ${y2} `;
      }
    }
    return d;
  }

  const maxX = Math.max(...nodes.map(n=>n.x)) + 140;
  const maxY = Math.max(...nodes.map(n=>n.y)) + 60;

  let svg = `<svg viewBox="0 0 ${maxX} ${maxY}" width="100%" style="max-width:1000px;">`;

  wires.forEach(w=>{ svg += `<path d="${pathForWire(w)}" fill="none" stroke="#94a3b8" stroke-width="1.6"/>`; });

  nodes.forEach(n=>{
    if(n.kind==='GATE' || n.kind==='OUTPUT'){
      inPoints(n).forEach(p=>{ svg += `<circle cx="${p.x}" cy="${p.y}" r="2" fill="#94a3b8"/>`; });
    }
  });

  nodes.forEach(n=>{
    if(n.kind==='INPUT'){
      svg += `<text x="${n.x-10}" y="${n.y+4}" fill="#e2e8f0" font-size="13" text-anchor="end" font-weight="600">${escapeHtml(n.label)}</text>`;
      svg += `<circle cx="${n.x}" cy="${n.y}" r="2.5" fill="#38bdf8"/>`;
    } else if(n.kind==='OUTPUT'){
      svg += `<text x="${n.x+10}" y="${n.y+4}" fill="#38bdf8" font-size="14" font-weight="700">F</text>`;
    } else if(n.kind==='GATE'){
      svg += drawGateNode(n);
    }
    // DUMMY nodes are pure routing waypoints and are not drawn.
  });

  svg += `</svg>`;
  return svg;
}

/* ============================================================
   TOP-LEVEL DRAW
============================================================ */
function setGateMode(mode){
  gateMode = mode;
  drawCircuit();
}

const GATE_MODE_NOTES = {
  simplified: 'Uses a practical mix of gates to keep the circuit simple.',
  basic: 'Uses only AND, OR, and NOT gates.',
  nand: 'Builds the whole circuit with NAND gates.',
  nor: 'Builds the whole circuit with NOR gates.'
};

function drawCircuit(){
  const svgWrap = document.getElementById('circuitWrap');
  const noteEl = document.getElementById('circuitNote');
  if(!lastResult){ svgWrap.innerHTML=''; return; }

  noteEl.textContent = GATE_MODE_NOTES[gateMode] || '';

  const graph = buildCircuitGraph(gateMode);
  if(graph.constMsg){
    svgWrap.innerHTML = `<p class="note">${escapeHtml(graph.constMsg)}</p>`;
    return;
  }

  computeLayers(graph.nodes);
  expandLongEdges(graph.nodes);
  orderLayers(graph.nodes);
  assignCoords(graph.nodes);
  refineY(graph.nodes);

  svgWrap.innerHTML = renderCircuitSVG(graph.nodes, graph.outputId);
}
