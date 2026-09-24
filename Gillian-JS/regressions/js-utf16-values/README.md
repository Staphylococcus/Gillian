# JavaScript UTF-16 value mapping

These 37 controls compile actual JavaScript and verify its runtime bodies in
`--total` mode. They cover arbitrary string concatenation, prefix cancellation,
`typeof`, symbolic property mutation/read, numeric property keys, and a wrong
concatenation result. They include arbitrary-input theorems and separate concrete
initialized-call witnesses. The latter do not bound the arbitrary-input proofs.
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
Actual JS length and charAt use typed checked primitives. Remaining symbolic
ordering, numeric code-unit, slicing and trim support stay separate obligations.

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

The `charat.js` caller executes the actual builtin with explicit method/scope
resources. It proves the correct code unit or empty string for arbitrary strings
and all Numbers, preserving ToInteger coercion and both range branches. Wrong
empty outcomes and a swapped surrogate claim reject. P06.2b1 below connects the
shared metadata context to actual initialization and proves its preservation.
Arbitrary repeated-call composition remains P06.2b2.
Core controls retain invalid-model rejection/recovery and replay five new
index/unit witnesses in concrete GIL. The index-one witness fixes a concrete
surrogate pair; four other queries retain symbolic index/string search. The PoC
requires native replay of those witnesses and all earlier artifacts. Some broad
false caller claims remain solver-incomplete and are retained there as diagnostic
evidence; no unknown result is counted as proof.

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
is introduced. Checked lookup and initialized context are established; arbitrary
repeated calls remain P06.2b2. Symbolic indexing is restricted to total mode.


P06.2b1 uses `CharAtContext.jsil` to describe the four actual String prototype
metadata fields, including `@primitiveValue`, and the charAt descriptor/builtin.
The arbitrary caller proves it preserves those resources. Full `Init.jsil`,
compiled from an empty closed entry, establishes the same context plus the real
caller function/scope metadata. Concrete initialized calls cover empty/outside,
NaN/infinite positions, ordinary units and surrogates. Wrong output, overwritten
method and changed method length must fail their postconditions. The native PoC
replay checks ten executable ASTs and both positive and mutated behaviors.

The summary-consuming `charat-twice.js` is registered only as an unchecked-callee
rejection (`--proc=twice`). Selecting both procedures and their proof dependency
still returns SMT unknown during result-summary definedness; that diagnostic
remains P06.2b2, not a positive proof. Native two-call parity is supplementary.
P06.2b1 passes the PoC frozen selection: 139 controls across six affected
jobs, including all 37 cases here, plus all required native replays and 120/120
PoC tests. Repeated-call composition remains P06.2b2.
