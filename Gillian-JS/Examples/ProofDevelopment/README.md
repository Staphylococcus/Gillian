# Pending exact-count proof

These inputs are not accepted regression cases. `ucs2length-exact.js` retains
the accepted AJV executable AST and original language-string entry. Its recursive
relation now receives the existing numeric length with an explicit equality to
the string length, avoiding the earlier mixed string/numeric bound query.
Automatic inverse witnesses then failed; explicit old-position/count fold
witnesses are checked proof annotations, not assumed results.

The parser now retains the trailing fold. Declaring predecessor witnesses in
`[step: #previous, #previous_count]` prevents an unnecessary inverse-arithmetic
discharge, including a signed-zero mismatch. The original successor relation
is still checked. Four compiled positive/rejection controls exercise that
existing label mechanism; no backend rule is changed.

The latest original-helper diagnostic completes several folds, then reaches its
90-second cap at a numeric count/position invariant (283 queries). It is not
exact-count acceptance. Earlier unknowns, parse errors and timeouts remain
retained in the sibling PoC's `count-witness-observations.json` and prior
`prefix-preservation-development.json`. The next obligation is documented in
`docs/full-proof-roadmap.md`. Exact count and its whole-helper rejection controls
must pass before these inputs enter the strict acceptance catalogue.
