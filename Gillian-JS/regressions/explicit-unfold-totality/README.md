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

The original focused positive has independently reviewed retained evidence.
The runner repair has offline tests only; the two native rejection controls
remain pending execution and independent review. No prior raw verdict is relabelled.

Run offline tests with `python3 -I -B test_runner.py`. Process calls are mocked;
finalization tests use the real pinned inventory helper over small temporary trees.
These tests are not symbolic proofs.

Before backend acceptance, separate controls must still cover mixed ordinary
errors, unclassified branch loss, both Matcher/PState simplification boundaries,
and affected recursive-lemma, predicate, definedness and closed-entry families.
The full validate10 caller and original finite-JSON admission remain open.
