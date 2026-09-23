# JavaScript UTF-16 value mapping

These sixteen controls compile actual JavaScript and verify its runtime bodies in
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
symbolic operations remain unsupported. Actual JS length now uses the typed
length primitive; character access and trim still have concrete-only externals.

The length controls explicitly import the actual `String.jsil` runtime body.
An unrestricted `s.length` proof returns `int_to_num(u16-len(s))`; it does not
assume a finite set of strings or a smaller analysis cap. The language string
domain makes that conversion exact, while generic GIL retains binary64 rounding.
A wrong constant-one postcondition is refuted; concrete controls reject byte
and code-point length for an astral pair. Empty/NUL/BMP/astral/lone-surrogate
parity is checked by the same ordinary JS body. The zero-result query currently
returns SMT unknown and is tested as incomplete, never as proof or refutation.
P06 must account for this sequence-length/Number solver limitation as it admits
indexing and additional comparisons. Core units retain exact boundary and
ties-to-even rounding controls without globally narrowing the UTF-16 domain.

Supporting checks also live in the core UTF-16 cases, frontend UTF-16/property
units, and existing JS code-unit, numeric, object, callback and serializer suites.
Run `python3 run.py` with `GILLIAN_JS` set to the built backend launcher.
