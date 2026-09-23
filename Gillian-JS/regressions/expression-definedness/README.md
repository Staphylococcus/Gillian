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

## Proof-term failures in total mode

Three proof-term fixtures also run in ordinary total and closed-entry modes:

- `proof-boolean-branch.gil`: a true disjunction must reach the failing assertion,
  even when its skipped operand contains an invalid list access.
- `proof-boolean-post.gil`: the negation of that true condition is a false
  postcondition and must reject.
- `proof-boolean-short-circuit.gil`: valid skipped operands and both proof
  branches retain their concrete Boolean behavior.

`Gillian-JS/test/proof_terms_tests.ml` checks the shared reducer against concrete
evaluation, required-operand error propagation, and the distinction between
failed assumption reduction and genuinely infeasible assumptions. These repairs
apply to total mode. They do not establish definedness for every symbolic proof
term; summary substitutions and entry/recursive ranks were separate gaps,
addressed in the next slice below.

## Proof-value domains (23 September)

Total verification now shares the executed-expression domain checker with
labelled substitutions and termination measures. Proof values admit logical
variables and abstract locations; executable syntax retains its leaf restrictions.
Missing domains raise an analysis failure before reduction can erase a partial
operation. Checks cover procedure entry/calls, loop abstraction/revisit, lemma
entry/induction reuse, and lemma arguments before rank instantiation.

Seventeen new GIL fixtures provide 18 controls, including a legacy-mode control.
They cover arbitrary/nonempty lists, program/logical substitutions, guarded and
skipped operands, valid-entry/invalid-call measures, weak loop generalization,
and an erased partial lemma argument. Failures must identify the intended
domain boundary. Four additional `proof_terms_tests` controls exercise shared
admission and direct invalid/valid loop-revisit states independently of entry.
These tests do not establish general assertion/matching definedness or full-fold
correctness; fold/unfold arguments and the broader proof-language audit remain open.

## Pure assertions and logical conditions

Total verification checks original `assert` expressions before entailment and
logical `if` conditions before evaluation or branch assumptions. Both reuse the
proof-value checker against the incoming state: a target assertion or a chosen
branch cannot establish its own missing domain. Missing domains report `Pure
assertion is not proved defined` or `Logical condition is not proved defined`.

Sixteen fixtures add 22 controls: program/logical variables, arbitrary/nonempty
lists, short-circuit guards, a domain established by an enclosing branch, a
failing symbolic sibling, empty/nonempty closed-entry cases, and legacy partial
mode. Existing Boolean branch-loss controls remain registered. These checks do
not cover fold/unfold arguments, separation-assertion matching, predicate bodies,
or pre/postcondition normalization.

The new checks also exposed eager list normalization below a rewritten Boolean
wrapper. In total mode that normalization now uses the reducer on the left Boolean
operand and normalizes the right unless the left proves it is skipped. Required
reads cannot be erased by a subsequent parent rewrite. Extended proof-term units
compare nested/negated short-circuit expressions with concrete evaluation and
retain required-operand failures.

Review adds ten fixtures and 17 controls. Length/reflexivity postconditions reject
required out-of-bounds reads but accept both skipped reads and valid required
reads, in ordinary and closed-entry mode. Branch-local variable assertions and
logical conditions accept skipped reads and reject required reads. The assertion
also retains its legacy partial-mode result.

Symbolic evaluation now respects total-mode short-circuiting during program
variable substitution, before touching the right operand. It reduces the left
operand and can use incoming path facts to prove that the right is skipped.
Three additional unit tests cover erasing parents for all three Boolean
operators, concrete/symbolic substitution parity, required variable failures,
and a nonliteral guard discharged from path facts. These are bounded repairs;
pre/postcondition domains in general remain open.

## Explicit Fold/Unfold arguments and Fold bindings

In total mode, explicit `fold`, `unfold` and `unfold*` arguments and Fold's
additional binding expressions now use the shared proof-value domain checker.
The check runs on each original expression against the incoming state, before
evaluation, matching or resource consumption can erase the term or supply its
missing domain. Unfold's additional bindings only rename variables. Missing
domains report `Fold argument`, `Unfold argument` or `Fold binding is not proved
defined`; partial mode retains its previous behavior.

Thirty-six fixtures add 45 controls: program/logical variables, arbitrary/nonempty
lists, short-circuit guards, enclosing-branch guards, branch-local variables,
recursive unfolding, legacy mode and a wrong Fold binding value that must still
fail matching. Concrete empty/nonempty entry procedures also run in ordinary
total mode. Their six closed-entry counterparts confirm the existing restriction
on explicit Fold/Unfold commands, for both valid and invalid arguments; they do
not reach the domain checker. The Unfold closed-entry fixtures reject their
setup Fold. This slice does not extend closed-entry's admitted proof language.

The initial AJV baseline exposed set literals/unions in existing object-key
predicates. Proof values now admit these two forms: every element is checked and
every union operand must have Set type. Six paired controls retain the partial
slice check inside these wrappers at all three boundaries. Three unit groups
cover typed/empty unions, duplicate elimination, invalid/untyped operands, hidden
partial elements and the retained executable-set restriction. Other logical set
operators remain outside this checker; no set execution model was added.

Predicate bodies, automatic unfolding, binder-aware assertion matching and
general pre/postcondition normalization still require separate domain audits.
