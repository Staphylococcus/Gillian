# JavaScript UTF-16 value mapping

These ten controls compile actual JavaScript and verify its runtime bodies in
`--total` mode. They cover arbitrary string concatenation, prefix cancellation,
`typeof`, symbolic property mutation/read, numeric property keys, and a wrong
concatenation result. Inputs are arbitrary represented values, not finite choices.
Value identity assertions preserve NaN and signed zero in property values.
The review regressions include an arbitrary-string comparison inside one branch
of a Boolean split: its unsupported ordering must stop analysis, never disappear
while the other branch establishes a false total proof. Its concrete witness
must fail the postcondition. Explicit literal fold witnesses must be lowered
alongside predicate arguments; the matching correct and wrong witnesses test
both outcomes. Core expression-transport tests cover GIL export/reimport,
including function-style `u16-nth` syntax.

JSIL string data, nested literals, type tests, proof annotations and `symb_string`
admission lower to the same GIL `Utf16` kind. Direct call identifiers remain GIL
byte names. Resolved dynamic calls accept the canonical payload of typed metadata.
Concrete properties preserve the key kind, matching symbolic properties; byte
keys cannot alias typed keys. GIL imports must explicitly use typed JS data.

Numeric formatting/parsing reuse the existing concrete routines and sound SMT
over-approximations in the new domain. Literal parser facts accompany typed
literals; the formatter roundtrip preserves numeric equality, including the NaN
case. Symbolic formatting is not claimed to produce an exact decimal spelling.
Legacy JSIL string ordering/indexing has concrete typed operations; unresolved
symbolic operations remain unsupported. Actual JS length, code-unit access and
trim still use the existing concrete-only externals. P05 length and P06 remain open.

Supporting checks also live in the core UTF-16 cases, frontend UTF-16/property
units, and existing JS code-unit, numeric, object, callback and serializer suites.
Run `python3 run.py` with `GILLIAN_JS` set to the built backend launcher.
