# Executed-expression definedness

The baseline falsely proved `unused-read.gil` in total mode even though the
empty list faults. A discarded or simplified-away result must not erase that
execution obligation. The recorded baseline output is in the PoC evidence.

List indexing, head/tail, repetition and slicing now require their operand types
and bounds before executable expression reduction. Checks follow actual PHI
operands and short-circuit guards. These controls include used/unused reads,
untyped inputs, negative/end indices, guarded reads and hidden partial terms.

The next slice adds scalar operand types, integer divide/remainder-by-zero,
finite integer conversion and constant byte-index checks. Symbolic byte indices
and integer shift domains remain unsupported. Boolean right operands are checked
only when evaluated. IEEE division by zero remains valid. Native action results
use the value-list constructor rather than being re-evaluated as code.

Signed quotient/remainder use Zarith truncation toward zero in both execution
and SMT. Division-builder cancellation no longer erases operations or reverses
quotients. The IsInt predicate uses finite integral binary64 semantics including
negative zero and values larger than an OCaml integer. Unit tests compare these
results with concrete evaluation. Pure proof-term domains still need a separate
audit. Ordinary proof mode retains its separate behavior. A proof-obligation failure alone is not a replayed
counterexample or the PoC's `disproved` verdict.

Symbolic NumToInt is admitted in total mode only after the executed-expression
check establishes a finite Number. Native IEEE round-to-integral (RTZ) followed
by exact real/integer conversion models truncation. Ordinary mode retains its
previous symbolic-conversion restriction. Controls cover list indices, bounds,
wrong results, NaN and infinity; solver incompleteness remains incompleteness.
