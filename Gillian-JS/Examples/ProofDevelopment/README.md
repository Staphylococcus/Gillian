# Pending exact-count proof

These inputs are not accepted regression cases. `ucs2length-exact.js` retains
the accepted AJV executable AST and original language-string entry. Its recursive
relation now receives the existing numeric length with an explicit equality to
the string length, avoiding the earlier mixed string/numeric bound query.
Automatic inverse witnesses then failed; explicit old-position/count fold
witnesses are checked proof annotations, not assumed results.

The trailing fold was dropped by the parser. The accepted parser slice repairs
its placement; the typed-capture probe executes it, then returns native SMT
unknown while matching a step and unfolding the prior prefix. Earlier SMT unknown,
case-cap and broken-pipe diagnostics remain non-proofs. Sources and next steps
are retained in the sibling PoC's `prefix-preservation-development.json` and
`docs/full-proof-roadmap.md`. Exact count and its intended rejection controls
must pass before these inputs enter the strict acceptance catalogue.
