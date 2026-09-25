# JavaScript UTF-16 value mapping

These controls compile actual JavaScript and verify its runtime bodies in
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

The summary-consuming `charat-twice.js` now has both a positive control selecting
and proving `check` and `twice` in dependency order, and the original unchecked-
callee rejection (`--proc=twice`). The wrong wrapper executes both calls and
then returns a Number in place of the required string; it must fail its
postcondition. Both share the unrestricted string/Number input precondition.
Independent-input direct calls remain solver-incomplete P06.2b2b work.
P06.2b1 passes the PoC frozen selection: 139 controls across six affected
jobs, including all 37 cases here, plus all required native replays and 120/120
PoC tests. Repeated-call composition remains P06.2b2.

P06.2b2a additionally checks two direct ordinary `charAt` calls with the same
arbitrary string/Number inputs. The final result and `CharAtContext` are proved
by executing both actual builtin bodies; a mutated second result must fail its
postcondition. Independent argument pairs and checked caller-summary composition
remain open P06.2b2b obligations. No backend implementation or proof domain is
changed by these two controls.
The affected frozen selection passes 141 controls across six jobs, including all
39 controls here, plus the six model artifacts, context/native replay and
120/120 PoC tests. All 46,982 frozen files remained unchanged.

P06.2b2b1 discharges guarded operand domains without eager
reachability checks for supported expressions. Unsupported operations and the
concrete byte-index bridge still require proof of deadness before skipping.
`SState.eval_expr` reduces formulas without program variables directly, retaining
the old path-sensitive evaluator if reduction encounters a partial term. The
full frozen PoC baseline passes 964 controls in 109 jobs, including all 41
controls here, 19 proof-term units, all six model replays and 120/120 PoC tests.
All 46,985 inputs remained unchanged. Earlier witness-unknown, case-timeout and
disk-exhaustion runs remain rejected and retained in the PoC summary report.
No new operation or domain assumption is added; independent input pairs remain
P06.2b2b work.

The runner allows 45 seconds per selected procedure (90 seconds for the two
checked helper/caller cases), recording each budget in its result. SMT query
limits are unchanged. Timeouts retain partial logs and fail acceptance.

P06.2b2b2 complete: `charat-independent.js` checks the actual helper and wrapper
with independently arbitrary string/Number pairs. Only the helper's proved
output type is made explicit; input identity still admits NaN and signed zero.
The wrong-result and unchecked-helper controls remain failures. A sufficient
entailment precheck accepts only subset UNSAT; SAT/unknown use the full query.
Definedness checking avoids constructing an unused final scratch context.
Complete-query feasibility may search for a validated native witness with
additional empty-string/zero guesses; a failed guess uses the full query.
Guesses never enter the symbolic state or narrow its original input contract.
The earlier no-op assumption shortcut was rejected and removed; matcher
consistency checking remains intact. Optional searches have separate bounded
budgets. No postcondition fact is removed from actual production.
The PoC independent-observations report passes 974 controls across all 109
supporting jobs, all six native model replays and 120/120 PoC tests. All 46,989
frozen inputs stayed unchanged. Final documentation follows validation; this is
not full-fold certification. Direct independent builtin calls remain pending.

P06.2b2b3 accepted: `charat-direct-independent.js` executes both builtin calls
directly over independent string/Number pairs. All nine paths prove on backend
`edf368e`; the mutation returning 42 has nine intended postcondition failures.
Both retain the existing 45-second single-procedure allowance. Native replay
binds 17 ASTs and 3,025 direct independent pairs. Focused frozen acceptance passes
135 controls across five jobs, all six model replays and 120/120 PoC tests, with
46,993 inputs unchanged. The PoC `direct-independent-observations.json` retains
source-bound evidence. Implementation, runtime and all binary bytes match the
published full 974-control baseline; this is a fixture/replay-only slice, not a
new full baseline or full-fold certification. Numeric code units are next.

P06.3 adds `Utf16CodeUnit` (`u16-code`) with the existing checked index domain
and exact unsigned 16-bit-to-binary64 observation. Actual `SP_charCodeAt` keeps
coercion, ToInteger and outside NaN while replacing the concrete-only external.
Seven actual-JS controls cover the unrestricted caller, three wrong-result claims
and full initialization/concrete calls. Source-bound acceptance passes 986
controls in 109 jobs, all seven model artifacts and 120/120 PoC tests. All 47,004
frozen inputs stayed unchanged. The PoC retains the failed concurrent run and
isolated passes; accepted four-job concurrency preserves all proof budgets. No
string/schema bound or helper axiom is added. Ranked actual traversal is next;
full JSON admission, helper composition and final adapters remain open.

The files in `../../Examples/ProofDevelopment/` remain unregistered development
inputs. The cursor-sign invariant and checked exit equality now permit one
successful exact-prefix total proof (106.32 seconds under a separate 300-second
diagnostic cap). Full-body mutation rejection and final case registration still
block acceptance; neither native solver limits nor existing case budgets change.
Unknowns/errors from negative controls are not accepted rejections.

Trailing proof-command controls cover function/block fallthrough, empty bodies,
loop backedges, both symbolic branches and code after a return. The parser keeps
trailing tactics on a synthetic empty statement at that exact list position;
false reachable assertions reject and an unreachable one stays unreachable.
Parser units also check comment order, disabled annotation parsing and rejection
of a dangling non-tactic annotation. These controls support the exact-helper
fold annotation; they do not prove its pending prefix theorem.

The four `count-witness*` controls exercise declared existential witnesses through
actual compiled JS. Symbolic integral counts and actual negative zero prove;
a wrong increment and a wrong supplied witness fail assertions. The declaration
makes the known predecessor available to matching-plan construction, avoiding
an extra inverse-arithmetic equality while retaining the original formula check.
These are focused witness controls, not the pending exact-count helper theorem.

## P07.1a2e — checked numeric advance

`Ucs2Arithmetic.gil` states one/two-increment preservation over arbitrary ordered
integral Numbers within the existing language-length bound. Callers must select
and prove `Ucs2NumericAdvance` in the same run before applying it. Two actual JS
callers increment count and position, then use the checked lemma. Double count
increments must fail their posts; a false arithmetic lemma and an unselected
lemma must also reject. All six cases retain the ordinary 45-second cap.
The original exact-prefix helper is still a development probe: a successful
arithmetic lemma alone does not prove exact Unicode count or the full fold.

All six new cases and six existing witness controls pass in focused validation.
Native replay checks 96 boundary/signed-zero inputs and the exact extra-increment
mutations. The current 108-case catalogue was not rerun in full; backend code and
binaries retain their previously accepted full-suite evidence.

## P07.1a2g — cursor signs and exit equality

Five new controls use the ordinary 45-second allowance. `length-zero-sign.js`
executes runtime string-length access over the original language-string domain
and proves its result is never negative zero; the opposite postcondition fails.
`cursor-exit.js` proves numeric exit bounds imply value identity when both sides
exclude negative zero. The two explicit signed-zero witnesses fail if either
guard is missing. This is necessary for substituting actual cursor/length values
in a predicate; numeric equality alone does not preserve zero's sign.

All five new controls and twelve existing arithmetic/witness cases pass. The
113-case catalogue has not been rerun in full. Backend implementation, installed
runtime and binary bytes retain the prior full-baseline evidence. The PoC's
`cursor-exit-observations.json` records focused checks and current limitations.

## P07.1a2i — accepted exact helper theorem

`ucs2length-exact.js` and `Ucs2Prefix.gil` are the canonical proof inputs,
promoted without changing the original body, entry, prefix definition or rank.
The strict case checks `Ucs2NumericAdvance` before use and has a new 180-second
allowance; all 113 old case budgets and native solver limits are unchanged.

The complete frozen run passes all 114 cases, including the exact helper
(130.26s), the existing safety helper (72.36s), and wrong-result rejection
(83.88s). Stalled progress, missing context and unchecked arithmetic lemmas reject.
All 11 concrete controls pass; native replay binds body and oracle ASTs to AJV.

Retaining known types for transitive query dependencies prevents an impossible
Number/Boolean alias. Complete-query optional witness searches additionally try
zero for Number variables not equated to expressions. Native validated SAT is
required; failed guesses fall back, without changing state or input contracts.
Positive aliases, contradictions, nonzero-counter fallback and required unknown
are checked in the core suite. Earlier unknown-producing candidates remain
rejected and retained in the sibling PoC.

The PoC's `exact-helper-observations.json` records 1,090 controls / 109 jobs,
120/120 PoC tests, nine model replays and 47,141 unchanged frozen inputs. Separate
complete-diff self-review found no actionable issue. This proves the helper's
exact greedy count, resources and termination; actual original-schema caller
composition and full-fold certification remain open.
