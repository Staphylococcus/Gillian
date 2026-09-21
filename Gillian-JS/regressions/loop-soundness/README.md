# Loop proof obligations

`broken-backedge.js` runs one loop iteration and returns `false`, but its
postcondition claims `42`. On the preceding build, Gillian printed the failed
invariant check at the back-edge, discarded that result, and reported success.
`mixed-exit.js` demonstrates the same false proof when another branch returns
successfully. This is a verifier bug, not an unresolved termination question.

The repair checks every invariant-establishment and preservation result before
continuing or closing a path. It also preserves errors when restoring loop
frames on exits, returns and throws. Empty result lists are explicit incomplete
proofs, and an invariant without compiler loop metadata cannot close a path.
Invariant failures retain their original diagnostic instead of replacing it
with the formula used to search for a counterexample.

Run the 17 controls and the independent concrete JavaScript checks:

```sh
GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/loop-soundness/run.py
node Gillian-JS/regressions/loop-soundness/concrete.cjs
```

`GILLIAN_JS` may name a wrapper adding the matching runtime path.
`GILLIAN_RESULTS_ROOT` chooses the output parent. Expected exit codes and failure
messages are checked; timeouts and unrelated errors do not pass. Positive cases
cover zero iterations, nested loops, framed locals, break, return and throw.
The report preserves the before/after evidence, source hashes and executable
identities, together with the other backend regressions.

This repairs **partial correctness**. The deliberately infinite `forever.js`
remains valid under partial verification because it never returns; `--total`
still rejects it and the other loops. Ranked-loop support remains pending:
capture a natural integer measure after invariant generalization, check strict
descent at every back-edge before closing the proof path, and ensure every
control-flow cycle crosses a checked loop header. Begin with a single natural
loop and reject unsupported entry/nesting patterns explicitly.
