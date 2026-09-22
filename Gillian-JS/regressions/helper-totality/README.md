# Total helper execution and pure proof closure

Run `GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/helper-totality/run.py`.
The runner checks exact exit/message pairs and keeps generated inputs/results.
Imported fixtures are copied into each isolated test directory.

Total verification may execute imported/unannotated helper bodies in full,
ignoring their partial/trusted summaries. It validates each reached instruction
and the helper CFG, rejects duplicate parameters, and retains every ordinary/error return and failing branch. A called helper's
body therefore contributes directly to the enclosing program proof. Missing or
extra arguments follow the existing concrete call-stack/arguments semantics in
this path. Calls USING proved summaries still require exact arity, including
calls originating inside helper bodies. Selected but unproved procedures remain
unavailable; a failed selected proof is never replaced by a trusted summary.

Pure assertions, logical conditionals and finite macro expansion are admitted.
Every reached nested proof command is checked; assume/produce/consume and
unreviewed predicate manipulation remain unsupported; defined fold/unfold
operations are covered by the separate predicate-totality suite. Macro expansion cycles
are rejected. In total mode an applied lemma must have every selected proof
case discharged earlier, or be the existing strictly smaller self-induction
hypothesis. Axioms, missing/empty proof coverage and failed conclusions cannot
supply summaries. These restrictions also apply while proving the lemmas.
Empty logical-command and summary-application result lists are incomplete,
except a contradictory checked self-induction hypothesis may close its branch
while independent base-case obligations remain checked.

The suite includes actual unchanged compiled JavaScript for an empty function
and `return 42`, plus an incorrect postcondition. Their emitted error-object
construction, GetValue and purge helpers execute under total-mode rules. The
primitive GPVUnfold macro branch is checked without assuming heap facts. This
establishes small compiled-JavaScript total proofs; it does not establish
arbitrary heap predicates, callbacks or the original classifier theorem.

Other controls cover helper loops, normal/error returns, repeated calls, ignored
false imported summaries, a fault alongside a successful branch, forbidden
operations, exact summary arity, and checked/missing/false/recursive lemmas.
General recursive helper summaries remain pending.

Resolved dynamic procedure IDs use the same checked summary or full-body rule on
every symbolic path. Unknown IDs are unsupported; non-procedure values are real
execution errors. No target is guessed from a contract. The controls include
branch-dependent targets, a bad branch, cycles, ranked and unranked recursion,
and an actual compiled JavaScript function-expression call with a false-post mutant.

Finite recursive helper call trees may be expanded completely, including mutual
and resolved dynamic recursion. Every leaf and branch must finish; reaching the
existing expansion/branch budget leaves the proof incomplete. No unfinished
path is dropped. This is full symbolic execution under the stated precondition,
not a termination summary for arbitrary recursive heaps. Selected recursive
summaries still require their checked rank. Cold unranked loop components may
be bypassed, but every entry into such a component is unsupported.
