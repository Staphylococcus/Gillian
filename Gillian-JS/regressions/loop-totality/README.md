# Checked natural-loop termination

Run `GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/loop-totality/run.py`.
The runner requires exact exit/message pairs; crashes and timeouts do not pass.

In `verify --total`, a GIL invariant can carry `variant(expression)` after its
binders. The expression uses only program variables represented in the invariant
and must evaluate to a nonnegative mathematical integer. Every loop-modified
local live across its header must occur in both the invariant and its binders.
Reads hidden in macros count as uses. Otherwise an omitted local could retain
its first-entry value and prove a false exit; the accumulator mutation controls
exercise this case. The entry value is
frozen **after** invariant generalization and protected from simplification.
Before closing each back-edge, the checker proves nonnegativity, strict descent
and invariant preservation. Failed or empty obligations retain their failures.

The checker derives a hierarchy from the actual procedure CFG. Every cyclic
component must have one entry through a ranked invariant. Removing that header
leaves acyclic paths or inner components that satisfy the same rule. Each header
gets its own frozen measure. Induction on nesting depth establishes that an
infinite execution would require infinitely many outer iterations, hence an
impossible descending natural sequence. Calls between headers still need the
existing totality rules. Irreducible entries and unranked hidden cycles fail.

Exiting a loop restores and removes exactly its frame; a direct transition to a
sibling loop restores the old frame before establishing the new invariant.
Suspended caller-store identities are protected against callee simplification.
Logical invariant binders that would rename saved caller/frame identities are
currently rejected; they need scoped renaming before admission. An empty JS
while-body marker retains its loop metadata, preserving ordinary loop checks.

Controls cover arbitrary integer countdown and finite-list traversal, multiple
back-edges, zero-entry/break/return paths, framed heap resources and proved
callees. Negative cases include non-progress, increasing/constant/negative/Num
ranks, weak or false invariants, false exits, failed callees, ghost/unbound ranks,
bypassed entries/cycles. Positive nested, sequential, adjacent, break and helper
loops have negative stalled-inner/stalled-outer and lost-state controls. The initially-five witness
that gets stuck at one prevents checking just the concrete first iteration.

JS annotation measures, scoped-heap measures, number/size bridges and full
compiled-JavaScript helper/proof closure remain pending. Existing JS/C
frontends preserve unranked invariants. The GIL syntax extension does not change
ordinary partial verification into a termination claim.
