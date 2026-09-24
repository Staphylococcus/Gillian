# Typed UTF-16 values

GIL `Utf16` values denote finite sequences of 16-bit code units. Their concrete
literal payload has a validated canonical CESU-8 representation. `u16"..."`
explicitly canonicalizes the literal's WTF-8 text; ordinary GIL string literals
remain bytes. `u16++` concatenates typed values and `u16-len` returns an exact
mathematical `Int`. There is no implicit byte/unit conversion or length cap.

These controls cover actual total verification, including arbitrary operands,
prefix cancellation, incorrect concatenation/length results and required type
failures in execution and proof terms. A guarded proof term and a skipped
short-circuit operand exercise the existing domain rules. Core units cover all
code-unit boundaries, wrapped identities, parser/JSON transport, concrete/SMT
agreement and actual `Smt.lift_model` recovery followed by concrete GIL replay.

Actual JS literals, admission, properties, typeof, length and charAt now use
this typed layer. `u16-nth` is checked in total mode: its index must be finite,
integral, nonnegative and below the mathematical sequence length. The symbolic
result is exactly one native code unit. Concrete evaluation compares exact
integer bounds before host conversion; no symbolic sequence cap is imposed.

The 45 controls include arbitrary valid-index proofs, a wrong unit, invalid
fractional/NaN/infinite/negative/end indices, discarded/self-compared accesses,
self-supporting proof terms and partial bound operands. Program-variable and
logical-variable types are stated explicitly in the positive primitive specs;
their equality already entails the same types, so this does not narrow inputs.
Ordinary verification rejects the new SMT encoding because its partial-operation
domain checks have not been audited. Core controls cover guarded conversion
boundaries, rounding/overflow, exact negated bounds and five lifted index/unit
witnesses with concrete replay. Full initialized caller context and the remaining
string operations stay separate roadmap work.

Run `python3 run.py` with `GILLIAN_JS` set to the built backend launcher.
