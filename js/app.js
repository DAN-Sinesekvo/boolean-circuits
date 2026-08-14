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
let numVars = 2;
let varNames = ['A','B'];
let truth = []; // array of {vals:[0/1,...], out: 0|1|'X'}
let lastResult = null; // {sopTerms, posTerms} from the last Generate
let gateMode = 'simplified';
let inputMode = 'truth';

/* ============================================================
   TABS / VAR COUNT
============================================================ */
function switchTab(which){
  inputMode = which;
  ['truth','expr','terms'].forEach(mode=>{
    const selected = mode===which;
    const tab = document.getElementById(`tab-${mode}`);
    tab.classList.toggle('active', selected);
    tab.setAttribute('aria-selected', String(selected));
    tab.tabIndex = selected ? 0 : -1;
    document.getElementById(`pane-${mode}`).classList.toggle('hidden', !selected);
  });
}

document.querySelector('.tabs').addEventListener('keydown', e=>{
  if(!['ArrowLeft','ArrowRight','Home','End'].includes(e.key)) return;
  const modes = ['truth','expr','terms'];
  let next = modes.indexOf(inputMode);
  if(e.key==='ArrowLeft') next=(next+modes.length-1)%modes.length;
  if(e.key==='ArrowRight') next=(next+1)%modes.length;
  if(e.key==='Home') next=0;
  if(e.key==='End') next=modes.length-1;
  e.preventDefault();
  switchTab(modes[next]);
  document.getElementById(`tab-${modes[next]}`).focus();
});

function onVarCountChange(){
  numVars = parseInt(document.getElementById('numVars').value);
  varNames = ['A','B','C','D','E','F'].slice(0,numVars);
  buildTruthTableUI();
  setExprAutoNote('');
  setTermsNote('');
}

function setTermsNote(msg, isError, inputId){
  const el = document.getElementById('termsNote');
  el.textContent = msg;
  el.classList.toggle('hidden', !msg);
  el.classList.toggle('error', !!isError);
  ['termsInput','dontCaresInput'].forEach(id=>{
    const invalid = !!isError && (!inputId || inputId===id);
    document.getElementById(id).setAttribute('aria-invalid', String(invalid));
  });
}

function updateTermNotation(){
  const kind = document.querySelector('input[name="termKind"]:checked').value;
  document.getElementById('termsPrefix').textContent = kind==='minterms' ? 'Σm(' : 'ΠM(';
  if(document.getElementById('termsNote').classList.contains('error')) setTermsNote('');
}

function setExprAutoNote(msg, isError){
  const el = document.getElementById('exprAutoNote');
  if(!el) return;
  el.textContent = msg;
  el.classList.toggle('hidden', !msg);
  el.classList.toggle('error', !!isError);
  document.getElementById('exprInput').setAttribute('aria-invalid', String(!!isError));
}

document.getElementById('exprInput').addEventListener('input', ()=>{
  if(document.getElementById('exprAutoNote').classList.contains('error')) setExprAutoNote('');
});
['termsInput','dontCaresInput'].forEach(id=>{
  document.getElementById(id).addEventListener('input', ()=>{
    if(document.getElementById('termsNote').classList.contains('error')) setTermsNote('');
  });
});

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
  if(inputMode==='expr'){
    const expr = document.getElementById('exprInput').value.trim();
    if(!expr){ setExprAutoNote('Enter an expression using variables A to F.', true); return; }
    let exprInfo;
    try{
      exprInfo = buildTruthFromExpression(expr);
    }catch(e){
      const message = e.isVarCountError || e.message==='Enter an expression using variables A to F.'
        ? e.message
        : 'Check the expression and try again.';
      setExprAutoNote(message, true);
      return;
    }
    setExprAutoNote(exprInfo.autoIncreased
      ? `Variable count changed to ${exprInfo.finalNumVars} to fit this expression.`
      : '');
    renderTruthTableUI(); // reflect into truth-table tab too
    // Also show the generated truth table alongside the results, for convenience.
    document.getElementById('truthTableResultWrap').innerHTML = buildTruthTableHTML(truth, false);
    document.getElementById('truthTableResultCard').classList.remove('hidden');
  } else if(inputMode==='terms') {
    const kind = document.querySelector('input[name="termKind"]:checked').value;
    let termsInfo;
    try{
      termsInfo = buildTruthFromTerms(kind, document.getElementById('termsInput').value, document.getElementById('dontCaresInput').value);
    }catch(e){
      setTermsNote(e.message, true, e.inputId);
      return;
    }
    numVars = termsInfo.finalNumVars;
    varNames = ['A','B','C','D','E','F'].slice(0,numVars);
    truth = termsInfo.truth;
    ensureNumVarOption(numVars);
    document.getElementById('numVars').value = String(numVars);
    setTermsNote(termsInfo.autoIncreased
      ? `Variable count changed to ${numVars} so index ${termsInfo.largestIndex} fits.`
      : '', false);
    renderTruthTableUI();
    document.getElementById('truthTableResultWrap').innerHTML = buildTruthTableHTML(truth, false);
    document.getElementById('truthTableResultCard').classList.remove('hidden');
  } else {
    setExprAutoNote('');
    setTermsNote('');
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
  document.getElementById('sopSteps').innerHTML = sopGroupLines.join('<br>') || 'No SOP groups — the output is always 0.';
  document.getElementById('posSteps').innerHTML = posGroupLines.join('<br>') || 'No POS groups — the output is always 1.';

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
