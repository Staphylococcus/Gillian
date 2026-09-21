# Initial procedure totality checks

`gillian-js verify --total` requires completion and the stated postcondition for
selected procedures in a deliberately small part of compiled GIL:

- Acyclic procedure control flow, with direct calls at exact arity.
- Self recursion with a mathematical integer variant that is nonnegative at
  entry and strictly decreases, remaining nonnegative, on every recursive call.
- Calls to other selected procedures only after all their proof cases pass.
- Reviewed JavaScript heap primitives, with the resource restrictions below.

The entry measure is captured under the same normalization as the precondition
and kept through later store updates and simplification. Variants use formal
program parameters, for example `variant(n)` or `variant(l-len xs)`, and must be
identical across the procedure's specification cases. Recursion uses Gillian's
existing summaries and integer entailment; it does not execute a bounded sample
of recursive calls.

```text
spec count(n)
[[ (n == #n) * types(#n : Int) * (0i i<= #n) ]]
[[ (ret == 0i) ]] variant(n) normal
proc count(n) {
  goto [n i> 0i] step done;
step: ret := "count"(n i- 1i);
  return;
done: ret := 0i;
  return
};
```

This proves termination and return value zero for every nonnegative mathematical
integer. `list.gil` proves the corresponding result for arbitrary finite GIL
lists. Their unchanged-argument mutants pass default partial verification and
fail total verification. Increasing the local counter before the call cannot
change the captured entry bound.

The JavaScript target admits `Alloc`, `GetCell`, `SetCell`, `DeleteCell`,
`DeleteObject`, `GetMetadata` and `GetAllProps` at their declared arities. These
native operations access finite heap maps or enumerate/sort finite property
lists; they execute no JavaScript callbacks. This reviewed primitive semantics
is part of the trusted backend, not a deduction about their OCaml implementations.
Other memory models default to admitting no actions. Logical producer/consumer
actions are not executable primitives for this purpose.

Total execution requires fresh allocation, string property keys, an exposed
property cell for writes/deletes, and the complete object footprint (including
metadata) before deleting an object. The legacy setter/deleter uses syntactic
keys, so a merely equal alias cannot satisfy the exposed-cell check. These
restrictions prevent logical resource construction from masquerading as safe
program execution. Predicate production/consumption and default partial mode are
unchanged. The unowned-write and invalid-key controls record that ordinary mode
currently accepts those cases; general repair of that legacy execution boundary
remains separate from admitting this restricted fragment.

`heap-list.gil` proves completion for arbitrary finite lists while allocating,
writing, reading and deleting an object on each recursive step. Its mutant stores
the unchanged list and fails the descent obligation. Symbolic-key controls cover
both present fields and the absent-field outcome; a wrong postcondition on one
field fails. A memory error on one branch cannot be hidden by another branch
returning successfully. Actions or recovery attempts producing no outcomes are
incomplete proofs.

The mode still rejects control-flow cycles, mutual recursion,
dynamic/parallel/external calls and logical commands other than `assert`.
`javascript-return.js` now passes the primitive gate but stops at the compiler's
`GPVUnfold` proof macro. Even an empty JavaScript function has a compiled
`TypeError` helper dependency and is rejected without its proof. Loop ranks,
proof annotations, helper/callback closure, JavaScript size measures, symbolic
UTF-16/JSON and full lowered-fold certification remain open.

Trusted-only, incomplete, omitted or failing callee specifications cannot justify
a totality result. Empty normalized proof coverage, suspended calls and exploration
budget exhaustion are incomplete proofs. Incremental mode is rejected to prevent
reuse of partial-correctness results. `--total` does not change the default mode.
Contradictory procedure postconditions now survive preprocessing as false proof
obligations, producing analysis failures instead of an internal exception.

Run all 65 positive, negative and partial-correctness controls:

```sh
GILLIAN_JS=gillian-js python3 Gillian-JS/regressions/procedure-totality/run.py
```

`GILLIAN_JS` may be a wrapper adding the matching runtime path.
`GILLIAN_RESULTS_ROOT` sets the output parent. Each result records the source hash,
command, output and expected exit/message; a timeout, crash or unrelated rejection
never satisfies a control. `observations.json` preserves the earlier 46-case
pure-GIL slice. `heap-observations.json` records the subsequent primitive-action
build, source hashes, 65 controls and lemma/numeric/unit regression runs.
