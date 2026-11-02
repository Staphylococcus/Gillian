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

## Atomic type conflicts (1 October 2026)

Explicit nonrecursive total-lemma unfolding now classifies an empty Types
production as infeasible only when an atomic value already has a different
known type. A reverse-typing failure alone is insufficient. The existing guard
still rejects unclassified empty outcomes; memory production and ordinary errors
are unchanged. Program and recursive-lemma contexts keep their existing behavior.

Four new fixtures use the same `answer`/`CheckChoice` selection shown above:

| Fixture | Required native outcome |
|---|---|
| typed-positive | rc0, lemma and caller succeed |
| typed-wrong-post | lemma postcondition failure, then unchecked-lemma rejection |
| typed-all-infeasible | rc124, no-outcomes rejection and no success |
| typed-unclassified | rc124, unclassified assertion-production loss and no success |

The last fixture requests Bool for an integer expression, not an atomic value.
It exercises the conservative boundary; it must not silently disappear. The
historical frozen runner above does not select these new fixtures. Invoke the
same verifier command with the desired fixture copied to case.gil.

Independent review also covers all five existing explicit-unfold fixtures and
the previously unsupported JSON scalar numeric-elimination theorem, whose
bytes are unchanged. Its false numeric conclusion genuinely fails. Eleven
native controls complete without unknowns/hard errors. The two passed controls
before a fixture syntax correction were reused, not replayed. A build-postcheck
count error was recovered from the successful primitive build; 381 production
compiled files match, and the 15 omitted old files are unselected test targets.

Evidence: `/tmp/codex-unfold-type-remaining-p04/independent-review.json`, SHA256
`360f3ede1185c0e1e5a106c029fe137a49f6a3019ef1a5ddf3730c8c9cafa5da`.
Source snapshot/build: `/tmp/codex-unfold-type-conflicts-p04/backend`;
verifier SHA256 `9617cea045df07e0f11395cb9681ae9ad3e2c5706dbdc62e39da37d3f4bed619`.
The primary checkout's older _build is not this candidate. Full JSON compound
admission and the final fold adapters remain open.
