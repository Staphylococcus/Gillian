# Binary64 natural loop measures

Run `GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/number-loop-totality/run.py`.
The controls require exact exit/message pairs, including explicit incomplete-proof
results. A timeout, crash or arbitrary assertion failure does not pass.

A total loop measure can be a mathematical `Int` or a `Num` proved finite,
integral and nonnegative using the existing binary64 semantics of `is_int` and
numeric comparison. Freeze its type and value after invariant generalization.
Every back-edge must keep that type, establish natural membership, and decrease
strictly under the appropriate comparison. A finite integral binary64 value
represents a mathematical natural, and strict IEEE comparison agrees with its
natural order. This gives well-founded descent without casting it to GIL `Int`.
The program's updates retain their actual IEEE rounding and overflow behavior.

Positive proofs cover all integral binary64 countdown inputs up to 2^32-1 and
2^53, signed zero with an explicit sign-preserving invariant, and forward indexing
through the full JavaScript array-length range. The forward measure is
`4294967295 - i`; 2^32-1 is the native maximum array length, not a small test bound.
The loop input/output conditions are unchanged by that measure choice.

Negative controls cover rounding stalls beyond the exact consecutive-integer
range, non-progress, increasing/fractional/negative/non-finite measures, changed
rank types and false postconditions. A finite Number is not implicitly a natural.

Two valid propositions remain incomplete with the current solver: the forward
loop using `len - i`, and a bounded mathematical-integer-to-binary64 step. These
controls require `Incomplete totality proof: SMT returned unknown`. Assertion
matching must preserve that result rather than label it a false postcondition.
No inverse-conversion rule, real-arithmetic approximation or unchecked lemma is
introduced to force these proofs through. Scoped JS annotation measures and the
logical JSON-size connection remain pending; these GIL proofs are not a theorem
of the original classifier.
