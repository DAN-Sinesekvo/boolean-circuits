/* ============================================================
   GATE MODE + CIRCUIT GRAPH BUILDING
   Every mode is restricted to 2-input gates. Candidate graphs come
   from truth-vector synthesis and several factored Boolean forms;
   the former SOP/POS construction remains as a guaranteed fallback.
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

/* ============================================================
   TRUTH-VECTOR SYNTHESIS
   Circuit selection is deliberately independent of the displayed SOP/POS.
   A bounded exact straight-line search handles small optimal circuits; a set
   of factored Boolean forms supplies deterministic fallbacks for larger ones.
============================================================ */
const SYNTH_LIMITS = {maxGates:4, maxStates:25000};

function circuitTruthSpec(){
  let value=0n, care=0n;
  const inputs=varNames.map(()=>0n);
  truth.forEach((row,i)=>{
    const bit=1n<<BigInt(i);
    if(row.out!=='X') care|=bit;
    if(row.out===1) value|=bit;
    row.vals.forEach((v,j)=>{ if(v) inputs[j]|=bit; });
  });
  const all=(1n<<BigInt(truth.length))-1n;
  return {value,care,all,inputs};
}

function synthesisLibrary(mode){
  if(mode==='basic') return {unary:['NOT'], binary:['AND','OR']};
  if(mode==='nand') return {unary:[], binary:['NAND']};
  if(mode==='nor') return {unary:[], binary:['NOR']};
  return {unary:['NOT'], binary:['AND','OR','NAND','NOR','XOR']};
}

function applyTruthGate(op,a,b,all){
  if(op==='NOT') return (~a)&all;
  if(op==='AND') return a&b;
  if(op==='OR') return a|b;
  if(op==='NAND') return (~(a&b))&all;
  if(op==='NOR') return (~(a|b))&all;
  return a^b;
}

function truthMatches(signal,spec){
  return ((signal^spec.value)&spec.care)===0n;
}

// Breadth-first enumeration of straight-line programs. A state holds every signal
// produced so far, so later gates may reuse a nonlinear intermediate (a real DAG,
// not merely an expression tree). Only fully explored frontiers imply optimality.
function searchExactCircuit(mode,spec){
  const library=synthesisLibrary(mode);
  const initialSignals=varNames.map((name,i)=>({truth:spec.inputs[i],depth:0,expr:{op:'VAR',name}}));
  const direct=initialSignals.find(s=>truthMatches(s.truth,spec));
  if(direct) return {expr:direct.expr,optimal:true};

  let frontier=[{signals:initialSignals}];
  let statesSeen=1;
  for(let gateCount=1;gateCount<=SYNTH_LIMITS.maxGates;gateCount++){
    const next=[];
    const seen=new Set();
    let best=null;
    let complete=true;
    outer: for(const state of frontier){
      const signals=state.signals;
      const proposals=[];
      library.unary.forEach(op=>signals.forEach((a,ai)=>{
        proposals.push({op,a,ai,truth:applyTruthGate(op,a.truth,0n,spec.all),depth:a.depth+1});
      }));
      library.binary.forEach(op=>{
        for(let ai=0;ai<signals.length;ai++){
          const start=(op==='NAND'||op==='NOR') ? ai : ai+1;
          for(let bi=start;bi<signals.length;bi++){
            const a=signals[ai], b=signals[bi];
            proposals.push({op,a,b,ai,bi,truth:applyTruthGate(op,a.truth,b.truth,spec.all),depth:Math.max(a.depth,b.depth)+1});
          }
        }
      });
      for(const p of proposals){
        if(signals.some(s=>s.truth===p.truth)) continue;
        const expr=p.op==='NOT' ? {op:p.op,a:p.a.expr} : {op:p.op,a:p.a.expr,b:p.b.expr};
        if(truthMatches(p.truth,spec) && (!best || p.depth<best.depth)) best={expr,depth:p.depth};
        const derived=signals.slice(varNames.length).map(s=>`${s.truth.toString(16)}/${s.depth}`);
        derived.push(`${p.truth.toString(16)}/${p.depth}`);
        derived.sort();
        const key=derived.join(',');
        if(seen.has(key)) continue;
        seen.add(key);
        next.push({signals:signals.concat({truth:p.truth,depth:p.depth,expr})});
        statesSeen++;
        if(statesSeen>=SYNTH_LIMITS.maxStates){ complete=false; break outer; }
      }
    }
    if(best) return {expr:best.expr,optimal:complete};
    if(!complete || next.length===0) return null;
    frontier=next;
  }
  return null;
}

function boolVar(name,comp){
  const v={op:'VAR',name};
  return comp ? {op:'NOT',a:v} : v;
}
function boolNot(a){
  if(a.op==='NOT') return a.a;
  if(a.op==='CONST') return {op:'CONST',value:1-a.value};
  return {op:'NOT',a};
}
function boolGate(op,a,b){
  if(!a) return b;
  if(!b) return a;
  if(op==='AND'){
    if(a.op==='CONST') return a.value ? b : a;
    if(b.op==='CONST') return b.value ? a : b;
  }
  if(op==='OR'){
    if(a.op==='CONST') return a.value ? a : b;
    if(b.op==='CONST') return b.value ? b : a;
  }
  if(op==='XOR'){
    if(a.op==='CONST') return a.value ? boolNot(b) : b;
    if(b.op==='CONST') return b.value ? boolNot(a) : a;
  }
  return {op,a,b};
}
function balanceBool(items,op){
  if(items.length===0) return {op:'CONST',value:op==='AND'?1:0};
  let queue=items.slice();
  while(queue.length>1){
    const next=[];
    for(let i=0;i<queue.length;i+=2) next.push(i+1<queue.length ? boolGate(op,queue[i],queue[i+1]) : queue[i]);
    queue=next;
  }
  return queue[0];
}
function sopBoolExpr(terms){
  return balanceBool(terms.map(t=>balanceBool(t.map(l=>boolVar(l.name,l.comp)),'AND')),'OR');
}
function posBoolExpr(factors){
  return balanceBool(factors.map(t=>balanceBool(t.map(l=>boolVar(l.name,l.comp)),'OR')),'AND');
}

function factoredSopExpr(terms){
  if(terms.length<=1) return sopBoolExpr(terms);
  const counts=new Map();
  terms.forEach(t=>t.forEach(l=>{
    const key=l.name+(l.comp?"'":'');
    counts.set(key,(counts.get(key)||0)+1);
  }));
  const choice=[...counts.entries()].filter(([,n])=>n>1).sort((a,b)=>b[1]-a[1]||a[0].localeCompare(b[0]))[0];
  if(!choice) return sopBoolExpr(terms);
  const key=choice[0];
  const selected=[], rest=[];
  terms.forEach(t=>{
    const index=t.findIndex(l=>l.name+(l.comp?"'":'')===key);
    if(index<0) rest.push(t);
    else selected.push(t.slice(0,index).concat(t.slice(index+1)));
  });
  const lit=terms.flat().find(l=>l.name+(l.comp?"'":'')===key);
  const grouped=boolGate('AND',boolVar(lit.name,lit.comp),factoredSopExpr(selected));
  return rest.length ? boolGate('OR',grouped,factoredSopExpr(rest)) : grouped;
}

function anfBoolExpr(spec){
  const coeff=truth.map((row,i)=>row.out===1 ? 1 : 0);
  for(let bit=0;bit<numVars;bit++){
    for(let mask=0;mask<coeff.length;mask++) if(mask&(1<<bit)) coeff[mask]^=coeff[mask^(1<<bit)];
  }
  // Avoid introducing implicit power rails into otherwise ordinary diagrams.
  if(coeff[0]) return null;
  const terms=[];
  for(let mask=1;mask<coeff.length;mask++) if(coeff[mask]){
    const vars=[];
    for(let bit=0;bit<numVars;bit++) if(mask&(1<<bit)) vars.push(boolVar(varNames[numVars-1-bit],false));
    terms.push(balanceBool(vars,'AND'));
  }
  const expr=balanceBool(terms,'XOR');
  return expr.op==='CONST' ? null : expr;
}

function shannonBoolExpr(){
  function rec(indices,level){
    const cared=indices.filter(i=>truth[i].out!=='X');
    if(cared.length===0) return {op:'CONST',value:0};
    const first=truth[cared[0]].out;
    if(cared.every(i=>truth[i].out===first)) return {op:'CONST',value:first};
    if(level>=numVars) return {op:'CONST',value:first};
    const zero=rec(indices.filter(i=>truth[i].vals[level]===0),level+1);
    const one=rec(indices.filter(i=>truth[i].vals[level]===1),level+1);
    const x=boolVar(varNames[level],false);
    if(JSON.stringify(zero)===JSON.stringify(one)) return zero;
    if(zero.op==='CONST'&&one.op==='CONST'){
      if(zero.value===0&&one.value===1) return x;
      if(zero.value===1&&one.value===0) return boolNot(x);
    }
    if(zero.op==='CONST'&&zero.value===0) return boolGate('AND',x,one);
    if(one.op==='CONST'&&one.value===0) return boolGate('AND',boolNot(x),zero);
    if(zero.op==='CONST'&&zero.value===1) return boolGate('OR',boolNot(x),one);
    if(one.op==='CONST'&&one.value===1) return boolGate('OR',x,zero);
    return boolGate('OR',boolGate('AND',boolNot(x),zero),boolGate('AND',x,one));
  }
  return rec(truth.map((_,i)=>i),0);
}

function graphFactory(){
  const nodes=[], inputCache=new Map(), gateCache=new Map(), exprCache=new WeakMap();
  let idCounter=0;
  function add(props){
    const node=Object.assign({id:'s'+(idCounter++),inputs:[]},props);
    node.depth=node.kind==='GATE' ? Math.max(...node.inputs.map(id=>nodes.find(n=>n.id===id).depth))+1 : 0;
    nodes.push(node); return node;
  }
  function input(name){
    if(!inputCache.has(name)) inputCache.set(name,add({kind:'INPUT',label:name,order:varNames.indexOf(name)}));
    return inputCache.get(name);
  }
  function gate(type,ids){
    const operands=(type==='NOT'?ids:ids.slice().sort());
    const key=type+'|'+operands.join('|');
    if(!gateCache.has(key)) gateCache.set(key,add({kind:'GATE',gateType:type,inputs:operands}));
    return gateCache.get(key);
  }
  return {nodes,input,gate,exprCache,add};
}

function graphFromPrimitive(expr){
  const f=graphFactory();
  function emit(e){
    if(e.op==='VAR') return f.input(e.name);
    if(f.exprCache.has(e)) return f.exprCache.get(e);
    const ids=[emit(e.a).id];
    if(e.op!=='NOT') ids.push(emit(e.b).id);
    const node=f.gate(e.op,ids); f.exprCache.set(e,node); return node;
  }
  const root=emit(expr);
  const output=f.add({kind:'OUTPUT',inputs:[root.id]});
  return {nodes:f.nodes,outputId:output.id};
}

function graphFromBoolean(expr,mode){
  const f=graphFactory();
  const memo=new Map();
  function emitConst(value){
    const a=f.input(varNames[0]);
    if(mode==='basic'){
      const na=f.gate('NOT',[a.id]);
      return f.gate(value?'OR':'AND',[a.id,na.id]);
    }
    const zero=f.gate('XOR',[a.id,a.id]);
    return value ? f.gate('NOT',[zero.id]) : zero;
  }
  function emit(e,comp=false){
    const key=(comp?'!':'')+JSON.stringify(e);
    if(memo.has(key)) return memo.get(key);
    let node;
    if(e.op==='CONST') node=emitConst(comp ? 1-e.value : e.value);
    else if(e.op==='VAR') node=comp ? f.gate('NOT',[f.input(e.name).id]) : f.input(e.name);
    else if(e.op==='NOT') node=emit(e.a,!comp);
    else if(e.op==='AND' || e.op==='OR'){
      const a=emit(e.a,false), b=emit(e.b,false);
      if(mode==='simplified') node=f.gate(comp ? (e.op==='AND'?'NAND':'NOR') : e.op,[a.id,b.id]);
      else {
        node=f.gate(e.op,[a.id,b.id]);
        if(comp) node=f.gate('NOT',[node.id]);
      }
    } else {
      const a=emit(e.a,false), b=emit(e.b,false);
      if(mode==='simplified') node=f.gate('XOR',[a.id,b.id]);
      else {
        const either=f.gate('OR',[a.id,b.id]);
        const both=f.gate('AND',[a.id,b.id]);
        const notBoth=f.gate('NOT',[both.id]);
        node=f.gate('AND',[either.id,notBoth.id]);
      }
      if(comp) node=f.gate('NOT',[node.id]);
    }
    memo.set(key,node); return node;
  }
  const root=emit(expr,false);
  const output=f.add({kind:'OUTPUT',inputs:[root.id]});
  return {nodes:f.nodes,outputId:output.id};
}

function graphFromBooleanRestricted(expr,mode){
  const f=graphFactory();
  const family=mode==='nand' ? 'NAND' : 'NOR';
  const memo=new Map();
  const invert=node=>f.gate(family,[node.id,node.id]);
  function emitConst(value){
    const a=f.input(varNames[0]), na=invert(a);
    if(family==='NAND'){
      const one=f.gate('NAND',[a.id,na.id]);
      return value ? one : invert(one);
    }
    const zero=f.gate('NOR',[a.id,na.id]);
    return value ? invert(zero) : zero;
  }
  function emit(e,comp=false){
    const key=(comp?'!':'')+JSON.stringify(e);
    if(memo.has(key)) return memo.get(key);
    let node;
    if(e.op==='CONST') node=emitConst(comp ? 1-e.value : e.value);
    else if(e.op==='VAR') node=comp ? invert(f.input(e.name)) : f.input(e.name);
    else if(e.op==='NOT') node=emit(e.a,!comp);
    else if(e.op==='AND'){
      if(family==='NAND'){
        node=f.gate('NAND',[emit(e.a,false).id,emit(e.b,false).id]);
        if(!comp) node=invert(node);
      } else {
        node=f.gate('NOR',[emit(e.a,true).id,emit(e.b,true).id]);
        if(comp) node=invert(node);
      }
    } else if(e.op==='OR'){
      if(family==='NOR'){
        node=f.gate('NOR',[emit(e.a,false).id,emit(e.b,false).id]);
        if(!comp) node=invert(node);
      } else {
        node=f.gate('NAND',[emit(e.a,true).id,emit(e.b,true).id]);
        if(comp) node=invert(node);
      }
    } else {
      const a=emit(e.a,false), b=emit(e.b,false);
      if(family==='NAND'){
        const t=f.gate('NAND',[a.id,b.id]);
        const u=f.gate('NAND',[a.id,t.id]);
        const v=f.gate('NAND',[b.id,t.id]);
        node=f.gate('NAND',[u.id,v.id]);
        if(comp) node=invert(node);
      } else {
        const t=f.gate('NOR',[a.id,b.id]);
        const u=f.gate('NOR',[a.id,t.id]);
        const v=f.gate('NOR',[b.id,t.id]);
        node=f.gate('NOR',[u.id,v.id]); // XNOR
        if(!comp) node=invert(node);
      }
    }
    memo.set(key,node); return node;
  }
  const root=emit(expr,false);
  const output=f.add({kind:'OUTPUT',inputs:[root.id]});
  return {nodes:f.nodes,outputId:output.id};
}

function circuitMetrics(graph){
  if(graph.constMsg) return {gateCount:0,depth:0,connections:0};
  const gates=graph.nodes.filter(n=>n.kind==='GATE');
  const root=graph.nodes.find(n=>n.id===graph.outputId);
  const source=root && graph.nodes.find(n=>n.id===root.inputs[0]);
  return {gateCount:gates.length,depth:source ? source.depth||0 : 0,
    connections:gates.reduce((sum,n)=>sum+n.inputs.length,0)};
}

function circuitMatchesTruth(graph,spec){
  if(graph.constMsg) return true;
  const values=new Map();
  graph.nodes.forEach(n=>{
    if(n.kind==='INPUT') values.set(n.id,spec.inputs[varNames.indexOf(n.label)]);
    else if(n.kind==='GATE'){
      const a=values.get(n.inputs[0]);
      const b=n.inputs.length>1 ? values.get(n.inputs[1]) : 0n;
      values.set(n.id,applyTruthGate(n.gateType,a,b,spec.all));
    } else if(n.kind==='OUTPUT') values.set(n.id,values.get(n.inputs[0]));
  });
  return truthMatches(values.get(graph.outputId),spec);
}

function circuitUsesLibrary(graph,mode){
  const library=synthesisLibrary(mode);
  const allowed=new Set(library.unary.concat(library.binary));
  return graph.nodes.every(n=>n.kind!=='GATE'||allowed.has(n.gateType));
}

function chooseCircuit(candidates){
  candidates.forEach((g,i)=>{ g._metrics=circuitMetrics(g); g._candidateOrder=i; });
  candidates.sort((a,b)=>a._metrics.gateCount-b._metrics.gateCount || a._metrics.depth-b._metrics.depth ||
    a._metrics.connections-b._metrics.connections || a._candidateOrder-b._candidateOrder);
  const chosen=candidates[0];
  chosen.gateCount=chosen._metrics.gateCount;
  chosen.depth=chosen._metrics.depth;
  delete chosen._metrics; delete chosen._candidateOrder;
  return chosen;
}

// Builds a full node graph {nodes, outputId, constMsg} for the given mode ('simplified',
// 'basic', 'nand', 'nor'). nodes: array of {id, kind:'INPUT'|'GATE'|'OUTPUT'|'DUMMY',
// gateType, label, inputs:[nodeId,...]}. Nodes are always pushed in dependency order
// (a node's inputs are always created before the node itself).
function buildLegacyCircuitGraph(mode){
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

function buildCircuitGraph(mode){
  const legacy=buildLegacyCircuitGraph(mode);
  if(legacy.constMsg){
    legacy.gateCount=0; legacy.depth=0;
    return legacy;
  }

  const candidates=[legacy];
  const spec=circuitTruthSpec();
  const exact=searchExactCircuit(mode,spec);
  if(exact){
    const graph=graphFromPrimitive(exact.expr);
    graph.exact=exact.optimal;
    candidates.push(graph);
  }

  const sopTerms=lastResult.sopTerms;
  const posFactors=lastResult.posTerms.map(posFactorLiterals);
  const forms=[sopBoolExpr(sopTerms),posBoolExpr(posFactors),boolNot(sopBoolExpr(lastResult.posTerms)),
    factoredSopExpr(sopTerms),shannonBoolExpr(),anfBoolExpr(spec)].filter(Boolean);
  forms.forEach(expr=>candidates.push(mode==='nand'||mode==='nor'
    ? graphFromBooleanRestricted(expr,mode) : graphFromBoolean(expr,mode)));

  return chooseCircuit(candidates.filter(graph=>circuitUsesLibrary(graph,mode)&&circuitMatchesTruth(graph,spec)));
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
    n.inputNets=[];
    n.inputs = n.inputs.map((srcId,inputIndex)=>{
      let cur = map.get(srcId);
      const netId=cur.netId||srcId;
      n.inputNets[inputIndex]=netId;
      while(n.layer - cur.layer > 1){
        const d = {id:'dum'+(dc++), kind:'DUMMY', inputs:[cur.id], inputNets:[netId],
          netId, layer:cur.layer+1};
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
    let out = `<path d="M ${x} ${y} L ${x+w} ${y+h/2} L ${x} ${y+h} Z" fill="var(--gate-fill)" stroke="var(--accent)" stroke-width="2"/>`;
    out += `<circle cx="${x+w+BR}" cy="${y+h/2}" r="${BR}" fill="var(--circuit-bg)" stroke="var(--accent)" stroke-width="2"/>`;
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
  let out = `<path d="${d}" fill="var(--gate-fill)" stroke="var(--accent)" stroke-width="2"/>`;
  if(n.gateType==='XOR'){
    out += `<path d="M ${x-6} ${y} q ${w*0.2} ${h/2} 0 ${h}" fill="none" stroke="var(--accent)" stroke-width="2"/>`;
  }
  out += `<text x="${x+w*0.16}" y="${n.y+4}" fill="var(--text)" font-size="10.5" font-weight="700">${n.gateType}</text>`;
  if(gateHasBubble(n.gateType)){
    // Same tangent-bubble treatment as NOT (see above).
    out += `<circle cx="${x+w+BR}" cy="${n.y}" r="${BR}" fill="var(--circuit-bg)" stroke="var(--accent)" stroke-width="2"/>`;
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
      wires.push({id:'w'+(wireId++), points:pts, srcLayer:src.layer,
        netId:(n.inputNets&&n.inputNets[idx])||src.netId||src.id});
    });
  });

  // Give every logical net one vertical lane in a layer gap. All branches from the
  // same source therefore share an aligned trunk instead of receiving unrelated bends.
  const layerGroups={};
  wires.filter(w=>w.points.length===4).forEach(w=>{
    (layerGroups[w.srcLayer]=layerGroups[w.srcLayer]||[]).push(w);
  });
  const junctions=[];
  Object.values(layerGroups).forEach(layerWires=>{
    const byNet=new Map();
    layerWires.forEach(w=>{
      if(!byNet.has(w.netId)) byNet.set(w.netId,[]);
      byNet.get(w.netId).push(w);
    });
    const netGroups=[...byNet.entries()].sort((a,b)=>{
      const ay=Math.min(...a[1].map(w=>w.points[0][1]));
      const by=Math.min(...b[1].map(w=>w.points[0][1]));
      return ay-by || String(a[0]).localeCompare(String(b[0]));
    });
    const gapStart=Math.min(...layerWires.map(w=>w.points[0][0]));
    const gapEnd=Math.max(...layerWires.map(w=>w.points[3][0]));
    netGroups.forEach(([netId,netWires],i)=>{
      const bx=gapStart+(i+1)/(netGroups.length+1)*(gapEnd-gapStart);
      netWires.forEach(w=>{ w.points[1][0]=bx; w.points[2][0]=bx; });
      if(netWires.length>1){
        const ys=new Set();
        netWires.forEach(w=>{ ys.add(w.points[0][1]); ys.add(w.points[3][1]); });
        ys.forEach(y=>junctions.push({x:bx,y,netId}));
      }
    });
  });

  // Flatten into H/V segments (tagged by wire) for crossing detection.
  const segs=[];
  wires.forEach(w=>{
    for(let i=0;i<w.points.length-1;i++){
      const [x1,y1]=w.points[i], [x2,y2]=w.points[i+1];
      if(y1===y2) segs.push({type:'H', wireId:w.id, netId:w.netId, y:y1, x1:Math.min(x1,x2), x2:Math.max(x1,x2)});
      else segs.push({type:'V', wireId:w.id, netId:w.netId, x:x1, y1:Math.min(y1,y2), y2:Math.max(y1,y2)});
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
          if(s.netId===w.netId || s.type!=='V') return;
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

  wires.forEach(w=>{ svg += `<path d="${pathForWire(w)}" fill="none" stroke="var(--wire)" stroke-width="1.6"/>`; });
  junctions.forEach(j=>{ svg += `<circle cx="${j.x}" cy="${j.y}" r="2.6" fill="var(--wire)"/>`; });

  nodes.forEach(n=>{
    if(n.kind==='GATE' || n.kind==='OUTPUT'){
      inPoints(n).forEach(p=>{ svg += `<circle cx="${p.x}" cy="${p.y}" r="2" fill="var(--wire)"/>`; });
    }
  });

  nodes.forEach(n=>{
    if(n.kind==='INPUT'){
      svg += `<text x="${n.x-10}" y="${n.y+4}" fill="var(--text)" font-size="13" text-anchor="end" font-weight="600">${escapeHtml(n.label)}</text>`;
      svg += `<circle cx="${n.x}" cy="${n.y}" r="2.5" fill="var(--accent)"/>`;
    } else if(n.kind==='OUTPUT'){
      svg += `<text x="${n.x+10}" y="${n.y+4}" fill="var(--accent)" font-size="14" font-weight="700">F</text>`;
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

  const graph = buildCircuitGraph(gateMode);
  const gateWord=graph.gateCount===1 ? 'gate' : 'gates';
  noteEl.textContent = `${GATE_MODE_NOTES[gateMode] || ''} ${graph.gateCount} ${gateWord} · depth ${graph.depth}.`;
  if(graph.constMsg){
    svgWrap.innerHTML = `<p class="constant-circuit">${escapeHtml(graph.constMsg)}</p>`;
    return;
  }

  computeLayers(graph.nodes);
  expandLongEdges(graph.nodes);
  orderLayers(graph.nodes);
  assignCoords(graph.nodes);
  refineY(graph.nodes);

  svgWrap.innerHTML = renderCircuitSVG(graph.nodes, graph.outputId);
}
