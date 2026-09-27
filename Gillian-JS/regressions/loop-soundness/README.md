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

Run the 22 controls and the independent concrete JavaScript checks:

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

The original failure-propagation repair establishes **partial correctness**.
The deliberately infinite `forever.js` remains valid under partial verification
because it never returns; `--total` rejects it and the unranked `valid-loop.js`.
A total loop proof additionally needs invariant establishment and preservation,
a nonnegative rank with strict descent on backedges, and coverage of every
control-flow cycle by a checked ranked header.

## Total-mode for-in header invariants

The compiler places a total-mode ForIn invariant immediately after the iteration
header PHI, before its guard. The enumeration prelude and non-total translation
are preserved. Establishment, preservation, rank and cycle checks remain active.

The three `for-in-unreachable*.js` controls pass on the compiled candidate:
the checked `False` invariant/rank 0 permits the unreachable branch's correct
postcondition, the wrong postcondition fails, and removing the annotation rejects
the unranked cycle. `Object.jsil` supplies the real enumeration helper body.
These cases do not prove a reached enumeration loop.

`ranked-true-entry.js` and `ranked-false-entry.js` differ only in their logical
invariant. Their ordinary `for` has a false test but a reached header: True passes,
while False fails invariant establishment before evaluating that test. The shared
header rule therefore checks an invariant even when the loop body cannot execute.

The original 17 regression cases also passed on this binary. Independently
reviewed original-AJV diagnostics retain five PHI-adjacent ranked headers and
backedges, reaching the later missing-specification guard; removing only the
ForIn annotation instead reaches the earlier cycle guard. Neither diagnostic
runs a procedure proof. These are scoped compiler/regression results, not a full
AJV, enumeration or finite-JSON theorem. See `observations.json` for source-bound
receipts, separate recovery reviews and compression mappings; no producer reran.
