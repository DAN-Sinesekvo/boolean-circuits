/* ============================================================
   OVERVIEW
   Pipeline: (truth table OR parsed expression) -> truth[] ->
   K-map render -> Quine-McCluskey (SOP from 1s, POS from 0s) ->
   gate graph (buildCircuitGraph) -> layered layout -> SVG.
   Everything runs client-side; no build step, no dependencies.
============================================================ */

/* ============================================================
   STATE
============================================================ */
let numVars = 3;
let varNames = ['A','B','C'];
let truth = []; // array of {vals:[0/1,...], out: 0|1|'X'}
let lastResult = null; // {sopTerms, posTerms} from the last Generate
let gateMode = 'simplified';

/* ============================================================
   TABS / VAR COUNT
============================================================ */
function switchTab(which){
  document.getElementById('tab-truth').classList.toggle('active', which==='truth');
  document.getElementById('tab-expr').classList.toggle('active', which==='expr');
  document.getElementById('pane-truth').classList.toggle('hidden', which!=='truth');
  document.getElementById('pane-expr').classList.toggle('hidden', which!=='expr');
}

function onVarCountChange(){
  numVars = parseInt(document.getElementById('numVars').value);
  varNames = ['A','B','C','D','E','F'].slice(0,numVars);
  buildTruthTableUI();
  setExprAutoNote('');
}

function setExprAutoNote(msg){
  const el = document.getElementById('exprAutoNote');
  if(!el) return;
  el.textContent = msg;
  el.classList.toggle('hidden', !msg);
}

function buildTruthTableUI(){
  truth = [];
  const rows = Math.pow(2,numVars);
  for(let i=0;i<rows;i++){
    const vals = [];
    for(let b=numVars-1;b>=0;b--) vals.push((i>>b)&1);
    truth.push({vals, out:0});
  }
  renderTruthTableUI();
}

// Builds one <table> for a slice of truth-table rows. indexOffset maps rows[0]
// back to its real index in `truth`, so click handlers toggle the correct row.
function buildSingleTruthTable(rows, interactive, indexOffset){
  let html = '<table><tr>';
  varNames.forEach(v=>html+=`<th>${v}</th>`);
  html += '<th>Out</th></tr>';
  rows.forEach((row,i)=>{
    const idx = indexOffset + i;
    html += '<tr>';
    row.vals.forEach(v=>html+=`<td>${v}</td>`);
    const cls = row.out===1?'v1':(row.out==='X'?'vx':'v0');
    if(interactive){
      html += `<td class="outcell ${cls}" onclick="cycleOut(${idx})">${row.out}</td>`;
    } else {
      html += `<td class="${cls}" style="font-weight:700;">${row.out}</td>`;
    }
    html += '</tr>';
  });
  html += '</table>';
  return html;
}

// Splits into two side-by-side tables once there are 32+ rows (5+ variables), since one long table gets unwieldy.
function buildTruthTableHTML(rows, interactive){
  if(rows.length >= 32){
    const half = rows.length/2;
    let html = '<div class="flex-cols">';
    html += '<div>' + buildSingleTruthTable(rows.slice(0,half), interactive, 0) + '</div>';
    html += '<div>' + buildSingleTruthTable(rows.slice(half), interactive, half) + '</div>';
    html += '</div>';
    return html;
  }
  return buildSingleTruthTable(rows, interactive, 0);
}

function renderTruthTableUI(){
  document.getElementById('truthTableWrap').innerHTML = buildTruthTableHTML(truth, true);
}

function cycleOut(i){
  const cur = truth[i].out;
  truth[i].out = cur===0?1:(cur===1?'X':0);
  renderTruthTableUI();
}

/* ============================================================
   MAIN GENERATE
============================================================ */
function generateAll(){
  const exprVisible = !document.getElementById('pane-expr').classList.contains('hidden');
  if(exprVisible){
    const expr = document.getElementById('exprInput').value.trim();
    if(!expr){ alert('Enter an expression.'); return; }
    let exprInfo;
    try{
      exprInfo = buildTruthFromExpression(expr);
    }catch(e){
      // A too-many-variables error is already a complete, specific message —
      // don't bury it behind a generic "could not parse" prefix.
      alert(e.isVarCountError ? e.message : ('Could not parse expression: '+e.message));
      return;
    }
    setExprAutoNote(exprInfo.autoIncreased
      ? `Note: this expression uses ${exprInfo.usedVars.length} variables (${exprInfo.usedVars.join(', ')}), `+
        `so the variable count was automatically increased to ${exprInfo.finalNumVars} to fit it.`
      : '');
    renderTruthTableUI(); // reflect into truth-table tab too
    // Also show the generated truth table alongside the results, for convenience.
    document.getElementById('truthTableResultWrap').innerHTML = buildTruthTableHTML(truth, false);
    document.getElementById('truthTableResultCard').classList.remove('hidden');
  } else {
    setExprAutoNote('');
    if(truth.length===0) buildTruthTableUI();
    document.getElementById('truthTableResultCard').classList.add('hidden');
  }

  const ones = [], zeros = [], dc = [];
  truth.forEach((row,i)=>{
    if(row.out===1) ones.push(i);
    else if(row.out===0) zeros.push(i);
    else dc.push(i);
  });

  // --- SOP: group the 1s ---
  const sopSteps = [];
  const sopQM = runQM(ones, dc, numVars);
  const sopChosen = ones.length===0 ? [] : selectEssential(sopQM.primeImplicants, ones, sopSteps);
  const sopTerms = ones.length===0 ? [] : sopChosen.map(pi=>termToSOPLiteral(pi.term));

  // --- POS: group the 0s (i.e. run QM treating zeros as the "ones" of F') ---
  const posSteps = [];
  const posQM = runQM(zeros, dc, numVars);
  const posChosen = zeros.length===0 ? [] : selectEssential(posQM.primeImplicants, zeros, posSteps);
  // each chosen term (a product-term of F') becomes a SUM term of inverted literals in POS of F
  const posTerms = zeros.length===0 ? [] : posChosen.map(pi=>termToSOPLiteral(pi.term));

  lastResult = {sopTerms, posTerms};

  // render K-map
  renderKmap();

  // render selected groups as simple "which rows/columns this box covers" lines,
  // instead of the full pass-by-pass Quine–McCluskey derivation.
  const sopGroupLines = sopChosen.map(pi=>{
    const label = literalsToString(termToSOPLiteral(pi.term), false) || '1';
    return `<b>${escapeHtml(label)}</b> — ${escapeHtml(groupBoxDescription(pi.term))}`;
  });
  const posGroupLines = posChosen.map(pi=>{
    const label = posFactorToString(termToSOPLiteral(pi.term));
    return `<b>${escapeHtml(label)}</b> — ${escapeHtml(groupBoxDescription(pi.term))}`;
  });
  document.getElementById('sopSteps').innerHTML = sopGroupLines.join('<br>') || '(no 1s to group — function is 0)';
  document.getElementById('posSteps').innerHTML = posGroupLines.join('<br>') || '(no 0s to group — function is 1)';

  // render expressions
  const sopStr = ones.length===0 ? '0' : sopTerms.map(lits=>literalsToString(lits,false)).join(' + ');
  const posStr = zeros.length===0 ? '1' : posTerms.map(posFactorToString).join('');
  document.getElementById('sopExpr').textContent = 'F = ' + sopStr;
  document.getElementById('posExpr').textContent = 'F = ' + posStr;

  document.getElementById('results').classList.remove('hidden');
  drawCircuit();
}

function escapeHtml(s){ return s.replace(/&/g,'&amp;').replace(/</g,'&lt;'); }

/* init */
buildTruthTableUI();
