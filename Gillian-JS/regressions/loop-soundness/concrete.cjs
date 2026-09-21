// The false proof concerns a terminating JS program, not a divergent execution.
const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const { join } = require('node:path');
const { createHash } = require('node:crypto');
const { runInNewContext } = require('node:vm');

const cases = [
  ['broken-backedge.js', 'check()', false],
  ['broken-backedge-correct-post.js', 'check()', false],
  ['mixed-exit.js', 'check(false)', false],
  ['mixed-exit.js', 'check(true)', true],
  ['nested-broken.js', 'check()', false],
];
const results = cases.map(([file, call, expected]) => {
  const source = readFileSync(join(__dirname, file), 'utf8');
  const actual = runInNewContext(`${source}\n${call}`, {}, { timeout: 1000 });
  assert.equal(actual, expected);
  return { file, call, expected, actual, passed: true,
    sourceSha256: createHash('sha256').update(source).digest('hex') };
});
console.log(JSON.stringify({ node: process.version, results }, null, 2));
