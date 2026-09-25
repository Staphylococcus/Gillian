# Actual compiled execution controls

The runner requires the expected process exit and final completion message.
It retains raw `output.bin` bytes and a SHA-256 receipt before decoding a readable
`output.log`. Lone UTF-16 surrogates can appear as non-UTF-8 bytes in diagnostic
state output; escaping them must not hide the execution verdict. Timeouts remain
failures, with partial output retained.

The five `ucs2length-*` programs execute the actual AJV helper body or one explicit
mutation. The positive runs all four witnesses; each negative checks one valid
string and throws with its actual wrong count. Initial count, skipped lone units,
double-counted pairs and incorrect non-low pairing are covered. These executions
are counterexamples, not universal proofs. The double-pair input replays the
retained symbolic model's units `0xd836, 0xdc0a`.

The sibling PoC's `replay-traversal.mjs` binds every full executable AST, including
the oracle harness, to the pinned AJV bundle and named mutation. It checks the
same results natively. Universal exact-count acceptance still requires the
unrestricted total proof from `Examples/ProofDevelopment/ucs2length-exact.js`;
these concrete witnesses do not restrict that proof's input domain.
