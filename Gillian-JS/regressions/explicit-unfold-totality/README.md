# Explicit-unfold totality controls

Three small GIL controls exercise checked-infeasible pruning during an explicit,
nonrecursive lemma unfold. They are backend regressions; they do not establish
an actual JavaScript or full-fold theorem.

## Run selected cases

The runner requires the retained, frozen backend and inventory helper named in
`run.py`. It verifies the immutable image ID and every backend pin before launch.
Use a **new output directory**, even when an earlier directory is empty:

```sh
UNFOLD_CARD=<card-id> python3 -I -B run.py \
  /home/vas/dev/Gillian/.worktrees/t_ae90afc3 \
  /tmp/unfold-controls-fresh \
  --cases wrong-post all-infeasible
```

Omit `--cases` to select all three in catalogue order. Explicit selections retain
argument order; duplicate and unknown cases are rejected. Each selected case runs
once; a failed control, input check or metadata check stops subsequent cases.
There are no retries. Each container has no network, two CPUs, 2 GiB memory and
an outer 45-second timeout (five-second kill grace).

The unchanged verifier selection is:

```sh
verify case.gil -a --total --dump-smt --logging=verbose \
  -R /work/_build/install/default/share/gillian-js/runtime \
  --proc=answer --lemma=CheckChoice
```

## Expected outcomes

- `positive`: exit 0, named CheckChoice and answer successes, all total specs
  succeeded, plus verbose evidence of unfolding `Choice(n)` and rejecting its
  impossible alternative at final admissibility.
- `wrong-post`: only the lemma postcondition changes from `#n == 0i` to
  `#n == 1i`. Require its explicit postcondition failure and a nonzero exit;
  downstream rejection of the unchecked lemma is allowed. Exit 124 can be valid
  for that diagnostic; timeout, crash or terminal SMT unknown cannot substitute.
- `all-infeasible`: three `#n == 0i` occurrences and the caller's `ret == 0i`
  change to 2; Choice's definitions and proof command stay unchanged. Require
  `Incomplete total proof: lemma produced no outcomes` and no named success.
  An earlier or different rejection is a failed control, not evidence of this
  empty-outcome guard.

## Evidence and current acceptance

All six source files, backend sources/binary/runtime, pin map and inventory
helper are frozen. Each staged case inventory is retained before its producer;
postchecks verify input membership, links and bytes, including the executed copy.
Primitive process receipts precede interpretation. Case reports retain offsets
qualified by `stdout` or `verbose`; generic verbose `Success:false` is not a
named proof verdict.

Final JSON survives handled runner and input-check failures. The retained-file
inventory includes file hashes and link destinations; an inventory failure is
explicitly incomplete. A successful top result requires every selected control
to execute and pass with unchanged inputs and complete evidence. All proof,
certification and full-proof flags remain false, even when controls pass.

The normal backend source patch is integrated after independent review of:

- the focused positive, wrong-post and all-infeasible controls;
- mixed surviving/error/infeasible alternatives;
- five isolated fault-injection controls for assertion production, first and
  remaining alternatives, Matcher simplification and PState simplification;
- 326 cases across predicate, lemma, helper, procedure and loop regression families;
- 21 sufficient-entailment tests, the required-query unknown control, and
  27 Binary64 plus 23 UTF-16 value tests;
- the actual nested AJV helper with checked zero-count inversion and both
  unchecked/false-lemma rejection controls.

Only the normal ten-file patch is integrated. Injected sources and binaries are
never used as a positive proof. The retained normal verifier is
`97cec1bff7752d995c39bf3adeca67c76c39678e9018325637c7f15b0c06b826` in
`.worktrees/t_ae90afc3`; its source bytes exactly match the integrated patch.
This source integration does not rebuild or replace the primary checkout's
existing executable. Reproduction continues to use the explicit frozen path.

The latest core units both exited 0. Their one-off driver's final inventory
used the wrong root for per-group `/results` links, so its original failure is
preserved. A separate mount-aware inventory and independent review verify all
183 result files and four links without rerunning the tests:
`/tmp/hermes-core-smt-units-p071/independent-review.json`.
The broader regression review is retained at
`/tmp/codex-hermes-takeover-review-p071/review.json`.

Run offline runner tests with `python3 -I -B test_runner.py`. These test the
receipt/classification harness, not symbolic proofs. Full `validate10` caller,
original finite-JSON admission and final full-fold adapters remain open.
