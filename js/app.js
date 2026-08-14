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
const truthTableViews = {
  editable: {expanded:false, rows:null, interactive:true, names:[]},
  result: {expanded:false, rows:null, interactive:false, names:[]}
};
const truthTableObservers = [];

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
  requestAnimationFrame(renderVisibleTruthTables);
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
  resetTruthTableExpansion();
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
  document.getElementById('termsInputLabel').textContent = kind==='minterms' ? 'Minterm indices' : 'Maxterm indices';
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
function buildSingleTruthTable(rows, interactive, indexOffset, names=varNames){
  let html = '<table><tr>';
  names.forEach(v=>html+=`<th>${v}</th>`);
  html += '<th>Out</th></tr>';
  rows.forEach((row,i)=>{
    const idx = indexOffset + i;
    html += '<tr>';
    row.vals.forEach(v=>html+=`<td>${v}</td>`);
    const cls = row.out===1?'v1':(row.out==='X'?'vx':'v0');
    if(interactive){
      html += `<td class="outcell ${cls}" onclick="cycleOut(${idx})">${row.out}</td>`;
    } else {
      html += `<td class="output-value ${cls}">${row.out}</td>`;
    }
    html += '</tr>';
  });
  html += '</table>';
  return html;
}

function resetTruthTableExpansion(){
  truthTableViews.editable.expanded = false;
  truthTableViews.result.expanded = false;
}

// Measure a real table with the current fonts and cell padding, then select the
// largest supported power-of-two layout that fits the destination container.
function measureTruthTableWidth(target, rows, names){
  if(!target.clientWidth || !rows.length) return 0;
  const probe = document.createElement('div');
  probe.style.cssText = 'position:absolute;visibility:hidden;width:max-content;pointer-events:none;';
  probe.innerHTML = buildSingleTruthTable(rows.slice(0,1), false, 0, names);
  target.appendChild(probe);
  const width = probe.querySelector('table').getBoundingClientRect().width;
  probe.remove();
  return width;
}

function chooseTruthTableColumns(target, rows, expanded, names){
  if(expanded || rows.length < 32) return 1;
  const maxColumns = rows.length >= 64 ? 4 : 2;
  const tableWidth = measureTruthTableWidth(target, rows, names);
  const available = target.clientWidth;
  const gap = 24;
  for(let columns=maxColumns; columns>=2; columns/=2){
    if(columns * tableWidth + (columns - 1) * gap <= available) return columns;
  }
  return 1;
}

function buildTruthTableHTML(rows, interactive, columns, expanded, viewName, names){
  const isLarge = rows.length === 32 || rows.length === 64;
  const collapsed = isLarge && columns === 1 && !expanded;
  const visibleRows = collapsed ? rows.slice(0,16) : rows;
  const chunkSize = Math.ceil(visibleRows.length / columns);
  let html = `<div class="truth-table-grid cols-${columns}${collapsed ? ' truth-table-collapsed' : ''}">`;
  for(let offset=0; offset<visibleRows.length; offset+=chunkSize){
    html += buildSingleTruthTable(visibleRows.slice(offset,offset+chunkSize), interactive, offset, names);
  }
  if(collapsed){
    html += '<div class="truth-table-more-row"><button type="button" class="truth-table-more" '
      + `onclick="expandTruthTable('${viewName}')" aria-label="Show all ${rows.length} truth table rows">`
      + 'Show more <svg viewBox="0 0 16 16" aria-hidden="true"><path d="M3.5 6 8 10.5 12.5 6" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg></button></div>';
  }
  html += '</div>';
  return html;
}

function renderTruthTable(target, rows, interactive, viewName, names=varNames){
  if(!target || !rows) return;
  const view = truthTableViews[viewName];
  view.rows = rows;
  view.interactive = interactive;
  view.names = names.slice();
  const columns = chooseTruthTableColumns(target, rows, view.expanded, view.names);
  target.innerHTML = buildTruthTableHTML(rows, interactive, columns, view.expanded, viewName, view.names);
}

function renderTruthTableView(viewName){
  const view = truthTableViews[viewName];
  const id = viewName==='editable' ? 'truthTableWrap' : 'truthTableResultWrap';
  const target = document.getElementById(id);
  if(view.rows && target && target.clientWidth){
    renderTruthTable(target, view.rows, view.interactive, viewName, view.names);
  }
}

function renderVisibleTruthTables(){
  renderTruthTableView('editable');
  renderTruthTableView('result');
}

function expandTruthTable(viewName){
  truthTableViews[viewName].expanded = true;
  renderTruthTableView(viewName);
}

function renderTruthTableUI(){
  renderTruthTable(document.getElementById('truthTableWrap'), truth, true, 'editable');
}

function renderResultTruthTable(){
  renderTruthTable(document.getElementById('truthTableResultWrap'), truth, false, 'result');
}

function canonicalNotation(prefix, indices, dontCares){
  return `F = ${prefix}(${indices.join(', ')}) + d(${dontCares.join(', ')})`;
}

function renderSourceResult(minterms, maxterms, dontCares){
  const showCanonicalTerms = inputMode==='truth';
  const truthWrap = document.getElementById('truthTableResultWrap');
  const canonicalWrap = document.getElementById('canonicalTermsResultWrap');
  document.getElementById('sourceResultHeading').textContent = showCanonicalTerms ? 'Canonical Terms' : 'Truth Table';
  truthWrap.classList.toggle('hidden', showCanonicalTerms);
  canonicalWrap.classList.toggle('hidden', !showCanonicalTerms);

  if(showCanonicalTerms){
    document.getElementById('canonicalMinterms').textContent = canonicalNotation('Σm', minterms, dontCares);
    document.getElementById('canonicalMaxterms').textContent = canonicalNotation('ΠM', maxterms, dontCares);
  } else {
    renderResultTruthTable();
  }
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
    resetTruthTableExpansion();
    renderTruthTableUI(); // reflect into truth-table tab too
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
    resetTruthTableExpansion();
    renderTruthTableUI();
  } else {
    setExprAutoNote('');
    setTermsNote('');
    if(truth.length===0) buildTruthTableUI();
  }

  const ones = [], zeros = [], dc = [];
  truth.forEach((row,i)=>{
    if(row.out===1) ones.push(i);
    else if(row.out===0) zeros.push(i);
    else dc.push(i);
  });

  renderSourceResult(ones, zeros, dc);

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
['truthTableWrap','truthTableResultWrap'].forEach(id=>{
  const target = document.getElementById(id);
  if(window.ResizeObserver){
    const observer = new ResizeObserver(renderVisibleTruthTables);
    observer.observe(target);
    truthTableObservers.push(observer);
  }
});
if(!window.ResizeObserver) window.addEventListener('resize', renderVisibleTruthTables);
