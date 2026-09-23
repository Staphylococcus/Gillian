# JavaScript UTF-16 value mapping

These 28 controls compile actual JavaScript and verify its runtime bodies in
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
parity is checked by the same ordinary JS body. The constant-zero result claim
is now refuted. Core units retain exact boundary and ties-to-even rounding
controls without globally narrowing the UTF-16 domain.

Supporting checks also live in the core UTF-16 cases, frontend UTF-16/property
units, and existing JS code-unit, numeric, object, callback and serializer suites.
Run `python3 run.py` with `GILLIAN_JS` set to the built backend launcher.

The `charat-lookup-unsupported.js` caller uses the actual builtin name/scope and
explicit prototype resources. Its arbitrary string/Number proof must remain
incomplete at `ExecuteStringNth`; assumed metadata is not initialization
proof. Core UTF-16 controls separately require native solver model validation:
a valid outside witness replays, an invalid inside witness aborts analysis,
and a subsequent ordinary query still succeeds. No symbolic `charAt` theorem
is claimed by these controls.

The single-comparison and full negative/outside/inside conditional controls
prove over arbitrary strings and every ToInteger position. Each wrong outcome
must fail its postcondition. The runtime numeric comparison retains its NaN
check and coercion order while omitting the redundant equality branch. Separate
less-than/less-or-equal fixtures prove their Boolean results for all Numbers,
including NaN, signed zeros and infinities, with wrong-result rejection controls.

The reducer canonicalizes only total length/ToInteger operations on typed
variables. An equivalent nonnegative-position conjunct in the SMT length
comparison keeps the earlier single-comparison proof complete. The UTF-16
primitive suite rejects wrong types and partial proof operands; core tests
retain conversion boundaries, exceptional-number parity, all three lifted
outcomes and invalid-model rejection/recovery. No input cap or helper assumption
is introduced. Initialized `charAt` and checked lookup remain P06.2.
