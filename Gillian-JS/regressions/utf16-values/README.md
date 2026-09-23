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

This is the typed GIL primitive layer. JS literals, symbolic admission, helpers,
property keys and runtime `typeof` still use the existing byte-backed JS values.
Their migration must preserve the same JS identity, not introduce independent
unit variables. Actual JS `s.length` and its binary64 conversion remain open.

Run `python3 run.py` with `GILLIAN_JS` set to the built backend launcher.
