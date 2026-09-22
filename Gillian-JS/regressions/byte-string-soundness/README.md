# Native byte-string controls

GIL strings use `(Seq (_ BitVec 8))` in SMT, preserving their actual byte
contents. Symbolic concatenation uses `seq.++`; `s-bytes` uses native `seq.map`
with an exact unsigned 8-bit to binary64 conversion. Concrete evaluation uses
the same 0..255 byte values. This supports generic byte reasoning; it does not
relabel bytes as UTF-16 code units. In particular, scalar UTF-8 and CESU-8 forms
remain distinct byte strings. The JS compiler's existing canonical encoding
supplies CESU-8 for actual JavaScript values.

Controls cover symbolic concatenation (including actual compiled JavaScript),
byte range and arbitrary finite scanning with a checked decreasing list length.
Wrong order, dropped input, a false 7-bit bound, stalled scans and false counts
must fail. Core unit tests additionally cover every byte value, NUL, surrogate
encodings, symbolic cancellation and recovering fresh counterexample strings.

The new map returns numbers through the existing GIL list representation.
Total-mode type matching may discharge a previously unknown type with an actual
entailment query. It never adds that type as an assumption. Remaining UTF-16
codec/trim/indexing and general expression-domain obligations are recorded in
the PoC verification backlog; this suite is not the classifier theorem.
