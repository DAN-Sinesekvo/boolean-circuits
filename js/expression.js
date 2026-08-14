/* ============================================================
   EXPRESSION PARSER (recursive-descent over tokens)
   Supports: variables (letters), ! prefix NOT, ' postfix NOT,
   . / & / juxtaposition AND, + / | OR, ^ XOR, parentheses.
============================================================ */
function tokenize(expr){
  const tokens = [];
  let i=0;
  while(i<expr.length){
    const c = expr[i];
    if(/\s/.test(c)){ i++; continue; }
    if(/[A-Za-z]/.test(c)){ tokens.push({t:'VAR', v:c.toUpperCase()}); i++; continue; }
    if(c==="'"){ tokens.push({t:'POSTNOT'}); i++; continue; }
    if(c==='!'){ tokens.push({t:'NOT'}); i++; continue; }
    if(c==='.'||c==='&'){ tokens.push({t:'AND'}); i++; continue; }
    if(c==='+'||c==='|'){ tokens.push({t:'OR'}); i++; continue; }
    if(c==='^'){ tokens.push({t:'XOR'}); i++; continue; }
    if(c==='('){ tokens.push({t:'LP'}); i++; continue; }
    if(c===')'){ tokens.push({t:'RP'}); i++; continue; }
    i++; // ignore unknown chars
  }
  // insert implicit AND between tokens like VAR/RP/POSTNOT-result followed by VAR/NOT/LP
  const out = [];
  for(let k=0;k<tokens.length;k++){
    out.push(tokens[k]);
    const cur = tokens[k], nxt = tokens[k+1];
    if(!nxt) continue;
    const curEndsValue = (cur.t==='VAR'||cur.t==='RP'||cur.t==='POSTNOT');
    const nxtStartsValue = (nxt.t==='VAR'||nxt.t==='NOT'||nxt.t==='LP');
    if(curEndsValue && nxtStartsValue) out.push({t:'AND'});
  }
  return out;
}

// Pratt-ish recursive descent. Precedence: POSTNOT/NOT > AND > XOR > OR
function parseExpr(tokens){
  let pos = 0;
  function peek(){ return tokens[pos]; }
  function next(){ return tokens[pos++]; }

  function parseOr(){
    let node = parseXor();
    while(peek() && peek().t==='OR'){ next(); node = {op:'OR', l:node, r:parseXor()}; }
    return node;
  }
  function parseXor(){
    let node = parseAnd();
    while(peek() && peek().t==='XOR'){ next(); node = {op:'XOR', l:node, r:parseAnd()}; }
    return node;
  }
  function parseAnd(){
    let node = parseUnary();
    while(peek() && peek().t==='AND'){ next(); node = {op:'AND', l:node, r:parseUnary()}; }
    return node;
  }
  function parseUnary(){
    if(peek() && peek().t==='NOT'){ next(); return {op:'NOT', l:parseUnary()}; }
    let node = parsePostfix();
    return node;
  }
  function parsePostfix(){
    let node = parsePrimary();
    while(peek() && peek().t==='POSTNOT'){ next(); node = {op:'NOT', l:node}; }
    return node;
  }
  function parsePrimary(){
    const tok = next();
    if(tok.t==='VAR') return {op:'VAR', name: tok.v};
    if(tok.t==='LP'){ const n = parseOr(); if(peek() && peek().t==='RP') next(); return n; }
    return {op:'VAR', name:'?'};
  }
  return parseOr();
}

function evalNode(node, env){
  switch(node.op){
    case 'VAR': return env[node.name];
    case 'NOT': return evalNode(node.l, env) ? 0 : 1;
    case 'AND': return (evalNode(node.l,env) && evalNode(node.r,env)) ? 1:0;
    case 'OR':  return (evalNode(node.l,env) || evalNode(node.r,env)) ? 1:0;
    case 'XOR': return (evalNode(node.l,env) ^ evalNode(node.r,env)) ? 1:0;
  }
}

function detectVarsInExpr(expr){
  const set = new Set();
  for(const c of expr) if(/[A-Za-z]/.test(c)) set.add(c.toUpperCase());
  return Array.from(set).sort();
}

// Keep the dropdown synchronized if callers ever supply a supported count that is
// not already represented in the markup.
function ensureNumVarOption(n){
  const sel = document.getElementById('numVars');
  const has = Array.from(sel.options).some(o=>o.value===String(n));
  if(!has){
    const opt = document.createElement('option');
    opt.value = String(n);
    opt.textContent = String(n);
    sel.appendChild(opt);
  }
}

function buildTruthFromExpression(expr){
  const usedVars = detectVarsInExpr(expr); // sorted alphabetically, e.g. ['A','C']
  if(usedVars.length===0) throw new Error('Enter an expression using variables A to F.');
  if(usedVars.length>6){
    const err = new Error(
      `Use no more than 6 variables. Found: ${usedVars.join(', ')}.`
    );
    err.isVarCountError = true;
    throw err;
  }

  // Only raise the selected variable count if the expression needs more than that.
  const selectedNumVars = parseInt(document.getElementById('numVars').value);
  let finalNumVars = selectedNumVars;
  let autoIncreased = false;
  if(usedVars.length > selectedNumVars){
    finalNumVars = usedVars.length;
    autoIncreased = true;
  }

  // If the selection has more variables than the expression uses, pad with unused
  // letters — QM will naturally drop them from the minimized result since F doesn't
  // depend on them.
  const fillerPool = ['A','B','C','D','E','F'].filter(l=>!usedVars.includes(l));
  const finalVars = usedVars.slice();
  while(finalVars.length < finalNumVars && fillerPool.length){
    finalVars.push(fillerPool.shift());
  }
  finalVars.sort();

  numVars = finalNumVars;
  varNames = finalVars;
  ensureNumVarOption(numVars);
  document.getElementById('numVars').value = String(numVars);

  const tokens = tokenize(expr);
  const ast = parseExpr(tokens);
  truth = [];
  const rows = Math.pow(2,numVars);
  for(let i=0;i<rows;i++){
    const vals = [];
    const env = {};
    for(let b=numVars-1, idx=0; b>=0; b--, idx++){
      const bit = (i>>b)&1;
      vals.push(bit);
      env[varNames[idx]] = bit;
    }
    const out = evalNode(ast, env);
    truth.push({vals, out});
  }
  return {autoIncreased, finalNumVars, usedVars, finalVars};
}
