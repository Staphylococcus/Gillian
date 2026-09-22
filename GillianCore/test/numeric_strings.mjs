// Regenerate the checked-in ECMAScript reference values with Node.
import { writeFileSync } from 'node:fs';
const strings = [
  '', ' ', '\t\r\n', '\u00a0\ufeff-0\u2029', '\u1680.5\u3000', '\u20001\u200a',
  '\u180e1', '\u00851', '1\u200b', '\ud800', ' \udfff ', '😀',
  '0', '-0', '+0', '00', '01', '+01', '1.', '.5', '-.5', '1e0', '1E+2', '1e-9999', '-1e-9999',
  '1e9999', '-1e9999', 'Infinity', '+Infinity', '-Infinity', 'infinity', 'inf', 'NaN', 'nan',
  '1_0', '1 0', '1e', '.', '+', '0x', '0x10', '0Xff', '+0x1', '-0x1', '0x1p2',
  '0o10', '0O77', '0o8', '0b10', '0B11', '0b2', '+0b1',
  '0xffffffffffffffffffffffffffffffff', '0b' + '1'.repeat(1100),
  '9007199254740993', '5e-324', '2.4703282292062327e-324',
];
let seed = 0x9e3779b97f4a7c15n;
for (let i = 0; i < 128; i++) {
  seed = BigInt.asUintN(64, seed * 6364136223846793005n + 1442695040888963407n);
  const bits = Buffer.alloc(8); bits.writeBigUInt64BE(seed);
  strings.push(String(bits.readDoubleBE()));
}
const values = strings.map(text => {
  const expected = Buffer.alloc(8); expected.writeDoubleBE(Number(text));
  return { units: Array.from({ length: text.length }, (_, i) => text.charCodeAt(i)), expectedBits: expected.toString('hex') };
});
writeFileSync(new URL('numeric_strings.json', import.meta.url), JSON.stringify({ node: process.version, values }, null, 2) + '\n');
