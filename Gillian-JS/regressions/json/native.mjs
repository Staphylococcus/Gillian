import { readFileSync } from 'node:fs';
import { runInNewContext } from 'node:vm';
import assert from 'node:assert/strict';
const model = readFileSync(new URL('../../runtime/JSON/json3.js', import.meta.url), 'utf8');
let assertions = 0;
for (const name of ['roundtrip', 'unicode', 'special-keys', 'exceptions', 'hooks', 'numbers', 'symbolic-choice', 'wrong-copy']) {
  const source = readFileSync(new URL(`${name}.js`, import.meta.url), 'utf8').replace(/^Assume\(.*\);$/m, '');
  for (const prefix of ['', model]) {
    for (const flag of name === 'symbolic-choice' ? [true, false] : [false]) {
      let failed = false;
      runInNewContext(prefix + '\n' + source, { symb: () => flag, Assert: ok => { assertions++; if (!ok) failed = true; } }, { timeout: 2000 });
      assert.equal(failed, name === 'wrong-copy', `${name} ${prefix ? 'model' : 'native'}`);
    }
  }
}
console.log(`${assertions} assertions checked against native JSON and the JS model.`);

// Deterministic differential corpus; these are tests, never proof witnesses for
// the whole unbounded JSON domain.
const candidate = {};
runInNewContext(model, { JSON: candidate });
let seed = 0x12345678;
const next = () => (seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0);
const keys = ['z', 'a', '__proto__', 'constructor', '10', '2', '01', '😀', '\ud800'];
function tree(depth) {
  if (!depth) return [null, true, false, 1000000000.5, 1e21, -0, 'é😀\ud800\u0000\n'][next() % 7];
  switch (next() % 3) {
    case 0: return tree(0);
    case 1: return Array.from({ length: next() % 4 }, () => tree(depth - 1));
    default: {
      const value = {};
      for (let n = next() % 4; n > 0; n--) Object.defineProperty(value, keys[next() % keys.length],
        { value: tree(depth - 1), enumerable: true, writable: true, configurable: true });
      return value;
    }
  }
}
for (let i = 0; i < 1000; i++) {
  const value = tree(3), expected = JSON.stringify(value);
  assert.equal(candidate.stringify(value), expected);
  assert.equal(JSON.stringify(candidate.parse(expected)), expected);
}
console.log('1000 seeded finite-tree differentials match native JSON.');
