/* Canonical minterm/maxterm input adapter. Produces the shared truth[] shape. */
function termsInputError(message, inputId){
  const error = new Error(message);
  error.inputId = inputId;
  return error;
}

function parseTermIndices(text, label, inputId){
  const trimmed = text.trim();
  if(!trimmed) return [];
  if(!/^\s*\d+(?:\s*(?:,\s*|\s+)\d+)*\s*$/.test(text)){
    throw termsInputError(`${label}: use whole numbers separated by commas or spaces.`, inputId);
  }
  const indices = Array.from(new Set(trimmed.split(/[\s,]+/).map(Number)));
  if(indices.some(index=>index>63)) throw termsInputError('Use indices from 0 to 63.', inputId);
  return indices;
}

function buildTruthFromTerms(kind, termsText, dontCaresText){
  if(kind !== 'minterms' && kind !== 'maxterms') throw new Error('Choose minterms or maxterms.');
  const terms = parseTermIndices(termsText, kind === 'minterms' ? 'Minterms' : 'Maxterms', 'termsInput');
  const dontCares = parseTermIndices(dontCaresText, "Don't-cares", 'dontCaresInput');
  const all = terms.concat(dontCares);
  const largestIndex = all.length ? Math.max(...all) : 0;

  const overlap = terms.filter(i=>dontCares.includes(i));
  if(overlap.length) throw new Error(`Indices ${overlap.join(', ')} appear in both lists. Keep each index in one list.`);

  const selectedNumVars = parseInt(document.getElementById('numVars').value,10);
  const requiredNumVars = largestIndex === 0 ? 1 : Math.ceil(Math.log2(largestIndex + 1));
  const finalNumVars = Math.max(selectedNumVars, requiredNumVars);
  if(finalNumVars > 6) throw new Error('Use no more than 6 variables.');

  const termSet = new Set(terms);
  const dcSet = new Set(dontCares);
  const generatedTruth = [];
  for(let i=0;i<Math.pow(2,finalNumVars);i++){
    const vals = [];
    for(let b=finalNumVars-1;b>=0;b--) vals.push((i>>b)&1);
    const out = dcSet.has(i) ? 'X' : (termSet.has(i) ? (kind === 'minterms' ? 1 : 0) : (kind === 'minterms' ? 0 : 1));
    generatedTruth.push({vals, out});
  }
  return {truth:generatedTruth, terms, dontCares, largestIndex, requiredNumVars, finalNumVars, autoIncreased:finalNumVars>selectedNumVars};
}
