/* ============================================================
   K-MAP RENDER (Gray-code layout, 2/3/4 variables)
============================================================ */
function grayCode(bits){
  const n = Math.pow(2,bits);
  const seq = [];
  for(let i=0;i<n;i++) seq.push(i ^ (i>>1));
  return seq;
}
function bitsToStr(val,bits){ return val.toString(2).padStart(bits,'0'); }

function mintermIndexFromBits(bitObj){
  // bitObj: array in order of varNames, MSB..LSB matches truth.vals ordering
  let idx=0;
  for(const b of bitObj) idx = (idx<<1)|b;
  return idx;
}

// Which variables run down the rows vs. across the columns of the K-map,
// for the current numVars. Shared by the K-map renderer and the group-box description.
function getKmapAxes(){
  let rowVars, colVars;
  if(numVars===2){ rowVars=[varNames[0]]; colVars=[varNames[1]]; }
  else if(numVars===3){ rowVars=[varNames[0]]; colVars=[varNames[1],varNames[2]]; }
  else if(numVars===4){ rowVars=[varNames[0],varNames[1]]; colVars=[varNames[2],varNames[3]]; }
  else if(numVars===5){ rowVars=[varNames[0],varNames[1],varNames[2]]; colVars=[varNames[3],varNames[4]]; }
  else { rowVars=[varNames[0],varNames[1],varNames[2]]; colVars=[varNames[3],varNames[4],varNames[5]]; }
  return {rowVars, colVars};
}

function renderKmap(){
  const wrap = document.getElementById('kmapWrap');
  const {rowVars, colVars} = getKmapAxes();

  const rowBits = rowVars.length, colBits = colVars.length;
  const rowGray = grayCode(rowBits), colGray = grayCode(colBits);

  let html = `<table><tr><th>${rowVars.join('')}\\${colVars.join('')}</th>`;
  colGray.forEach(c=>html+=`<th>${bitsToStr(c,colBits)}</th>`);
  html += '</tr>';

  rowGray.forEach(r=>{
    html += `<tr><th>${bitsToStr(r,rowBits)}</th>`;
    colGray.forEach(c=>{
      // reconstruct full bit vector in varNames order
      const rBitsArr = bitsToStr(r,rowBits).split('').map(Number);
      const cBitsArr = bitsToStr(c,colBits).split('').map(Number);
      const full = rBitsArr.concat(cBitsArr);
      const idx = mintermIndexFromBits(full);
      const val = truth[idx].out;
      const cls = val===1?'v1':(val==='X'?'vx':'v0');
      html += `<td class="kmapcell ${cls}">${val}</td>`;
    });
    html += '</tr>';
  });
  html += '</table>';
  wrap.innerHTML = html;
}

/* ============================================================
   QUINE-McCLUSKEY
============================================================ */
function countOnes(s){ let c=0; for(const ch of s) if(ch==='1') c++; return c; }

function combinable(a,b){
  if(a.length!==b.length) return null;
  let diff=-1;
  for(let i=0;i<a.length;i++){
    if(a[i]!==b[i]){
      if(a[i]==='-'||b[i]==='-') return null; // dash positions must match
      if(diff!==-1) return null; // more than one difference
      diff=i;
    }
  }
  if(diff===-1) return null;
  return a.substring(0,diff)+'-'+a.substring(diff+1);
}

function runQM(targetMinterms, dontCares, bits){
  // returns {primeImplicants: [{term, minterms:Set}], stepsLog: [string,...]}
  const allTerms = new Map(); // term -> Set(minterms)
  const initial = new Set([...targetMinterms, ...dontCares]);
  let currentGroups = {}; // count of ones -> array of {term, minterms:Set}
  initial.forEach(m=>{
    const term = m.toString(2).padStart(bits,'0');
    const ones = countOnes(term);
    if(!currentGroups[ones]) currentGroups[ones]=[];
    currentGroups[ones].push({term, minterms:new Set([m])});
  });

  const primeImplicants = new Map(); // term -> minterms Set
  const stepsLog = [];
  let pass=1;

  while(true){
    const keys = Object.keys(currentGroups).map(Number).sort((a,b)=>a-b);
    if(keys.length===0) break;
    const nextGroups = {};
    const used = new Set();
    let anyCombined = false;
    stepsLog.push(`--- Pass ${pass}: grouping by number of 1s ---`);

    for(let gi=0; gi<keys.length-1; gi++){
      const g1 = currentGroups[keys[gi]] || [];
      const g2 = currentGroups[keys[gi+1]] || [];
      for(const a of g1){
        for(const b of g2){
          const combined = combinable(a.term,b.term);
          if(combined){
            anyCombined = true;
            used.add(a.term+'|'+[...a.minterms].sort().join(','));
            used.add(b.term+'|'+[...b.minterms].sort().join(','));
            const key = countOnes(combined); // group next pass by number of 1s (dashes count as 0)
            if(!nextGroups[key]) nextGroups[key]=[];
            const unionM = new Set([...a.minterms, ...b.minterms]);
            // avoid duplicate combined term in same group
            let existing = nextGroups[key].find(x=>x.term===combined);
            if(existing){ unionM.forEach(m=>existing.minterms.add(m)); }
            else nextGroups[key].push({term:combined, minterms:unionM});
            stepsLog.push(`${a.term} (m:${[...a.minterms].join(',')}) + ${b.term} (m:${[...b.minterms].join(',')}) → ${combined}`);
          }
        }
      }
    }

    // anything not used in this pass is a prime implicant
    keys.forEach(k=>{
      (currentGroups[k]||[]).forEach(item=>{
        const sig = item.term+'|'+[...item.minterms].sort().join(',');
        if(!used.has(sig)){
          if(!primeImplicants.has(item.term)) primeImplicants.set(item.term, new Set());
          item.minterms.forEach(m=>primeImplicants.get(item.term).add(m));
        }
      });
    });

    if(!anyCombined) break;
    currentGroups = nextGroups;
    pass++;
  }

  const piList = [...primeImplicants.entries()].map(([term,mset])=>({term, minterms:mset}));
  return {primeImplicants: piList, stepsLog};
}

function selectEssential(piList, requiredMinterms, stepsLog){
  const required = new Set(requiredMinterms);
  const chosen = [];
  const covered = new Set();

  // essential PI pass
  requiredMinterms.forEach(m=>{
    const covering = piList.filter(pi=>pi.minterms.has(m));
    if(covering.length===1){
      const pi = covering[0];
      if(!chosen.includes(pi)){
        chosen.push(pi);
        pi.minterms.forEach(x=>{ if(required.has(x)) covered.add(x); });
        stepsLog.push(`Minterm ${m} is only covered by ${pi.term} → essential prime implicant.`);
      }
    }
  });

  // greedy cover remaining
  let remaining = requiredMinterms.filter(m=>!covered.has(m));
  while(remaining.length>0){
    let best=null, bestCount=-1;
    for(const pi of piList){
      if(chosen.includes(pi)) continue;
      const cnt = remaining.filter(m=>pi.minterms.has(m)).length;
      if(cnt>bestCount){ bestCount=cnt; best=pi; }
    }
    if(!best || bestCount<=0) break;
    chosen.push(best);
    stepsLog.push(`Greedily selecting ${best.term} to cover remaining minterms: ${remaining.filter(m=>best.minterms.has(m)).join(',')}`);
    remaining = remaining.filter(m=>!best.minterms.has(m));
  }
  return chosen;
}

function termToSOPLiteral(term){
  const lits = [];
  for(let i=0;i<term.length;i++){
    if(term[i]==='1') lits.push({name:varNames[i], comp:false});
    else if(term[i]==='0') lits.push({name:varNames[i], comp:true});
  }
  return lits; // empty means constant 1
}

// Does K-map row/col header string s (e.g. "01") match a QM term pattern (e.g. "0-")?
// '-' in the pattern means "don't care about this bit" (any value matches).
function patternMatches(headerStr, pattern){
  for(let i=0;i<pattern.length;i++){
    if(pattern[i]!=='-' && pattern[i]!==headerStr[i]) return false;
  }
  return true;
}

// Describes a selected QM term (e.g. "1-0") as the actual rows/columns of the K-map
// it spans — e.g. "Rows 10, 11 · Columns 00" — instead of the full grouping derivation.
function groupBoxDescription(term){
  const {rowVars, colVars} = getKmapAxes();
  const rowBits = rowVars.length, colBits = colVars.length;
  const rowPattern = term.substring(0, rowBits);
  const colPattern = term.substring(rowBits);
  const rowHeaders = grayCode(rowBits).map(v=>bitsToStr(v,rowBits)).filter(s=>patternMatches(s,rowPattern));
  const colHeaders = grayCode(colBits).map(v=>bitsToStr(v,colBits)).filter(s=>patternMatches(s,colPattern));
  const rowsStr = rowHeaders.length===Math.pow(2,rowBits) ? 'all' : rowHeaders.join(', ');
  const colsStr = colHeaders.length===Math.pow(2,colBits) ? 'all' : colHeaders.join(', ');
  return `Rows ${rowsStr} · Columns ${colsStr}`;
}

function literalsToString(lits, comp){
  if(lits.length===0) return '1';
  return lits.map(l=>l.name + ((l.comp!==comp)?"'":'')).join('');
}

// Converts one QM term of F' into its POS factor: by De Morgan, the OR of the
// complemented literals. An empty literal list means F' \u2261 1, whose dual is
// the constant 0 (not '1').
function posFactorToString(lits){
  if(lits.length===0) return '0';
  return '(' + lits.map(l=>l.name + (!l.comp?"'":'')).join(' + ') + ')';
}
