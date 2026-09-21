import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';
import assert from 'node:assert/strict';

let assertions = 0;
for (const name of ['concrete', 'coercion', 'loop-exception', 'ordering', 'operations', 'construction-coercion', 'literal-values', 'generated-code', 'generated-lone-source', 'wrong-code-point', 'symbolic-choice']) {
  // Only replace the analysis directive; execute the same JS body in Node.
  const source = readFileSync(new URL(`${name}.js`, import.meta.url), 'utf8')
    .replace(/^Assume\(.*\);$/m, '');
  for (const flag of name === 'symbolic-choice' ? [true, false] : [false]) {
    let failed = false;
    runInNewContext(source, {
      symb: () => flag,
      Assert: ok => { assertions++; if (!ok) failed = true; },
    }, { timeout: 1000 });
    assert.equal(failed, name === 'wrong-code-point', name);
  }
}
console.log(`${assertions} native assertions checked, including the expected negative control.`);
