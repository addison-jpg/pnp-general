// Tokenizes every .ath file in the repo with the grammar; fails on invalid.illegal
// tokens, unbalanced circuit/end, or any non-space text left with no scope.
const fs = require('fs'), path = require('path');
const vsctm = require('vscode-textmate'), onig = require('vscode-oniguruma');
const root = path.resolve(__dirname, '../../..');
const wasm = fs.readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm')).buffer;
const lib = onig.loadWASM(wasm).then(() => ({
  createOnigScanner: p => new onig.OnigScanner(p),
  createOnigString: s => new onig.OnigString(s)
}));
const registry = new vsctm.Registry({
  onigLib: lib,
  loadGrammar: async n => n === 'source.asteroid'
    ? vsctm.parseRawGrammar(fs.readFileSync(path.join(__dirname, '../syntaxes/asteroid.tmLanguage.json'), 'utf8'), 'g.json') : null
});
function walk(d, out) {
  for (const e of fs.readdirSync(d, { withFileTypes: true })) {
    if (e.name === '.git' || e.name === 'node_modules') continue;
    const p = path.join(d, e.name);
    if (e.isDirectory()) walk(p, out); else if (e.name.endsWith('.ath')) out.push(p);
  }
  return out;
}
(async () => {
  const g = await registry.loadGrammar('source.asteroid');
  const files = walk(root, []);
  let bad = 0, toks = 0;
  for (const f of files) {
    let st = vsctm.INITIAL;
    const lines = fs.readFileSync(f, 'utf8').split('\n');
    lines.forEach((line, i) => {
      const r = g.tokenizeLine(line, st);
      for (const t of r.tokens) {
        const txt = line.slice(t.startIndex, t.endIndex);
        if (!txt.trim()) continue;
        toks++;
        const last = t.scopes[t.scopes.length - 1];
        if (/invalid/.test(last) || t.scopes.length === 1) {
          bad++; console.log(`${path.relative(root, f)}:${i + 1}: ${JSON.stringify(txt)} -> ${last}`);
        }
      }
      st = r.ruleStack;
    });
    // circuit block must be closed at EOF (stack back to the root grammar only)
    if (st.depth > 1) { bad++; console.log(`${path.relative(root, f)}: unterminated circuit (no 'end')`); }
  }
  console.log(`${files.length} files, ${toks} tokens, ${bad} problems`);
  process.exit(bad ? 1 : 0);
})();
