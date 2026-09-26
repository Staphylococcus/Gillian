# mixed-errors: ordinary errors survive infeasible unfold branches

Scope: P07.1a3b. Two new fixtures added to
`Gillian-JS/regressions/explicit-unfold-totality/`; no engine, runtime, or
backend change. The driver/launcher in `/tmp/hermes-unfold-mixed-errors-p071/`
is immutable (SHA-pinned); its in-memory classifier carries the new
expectations. The frozen backend is unchanged.

## Fixture design

`Choice` has three clauses `n==0, n==1, n==2`; the interval `0<=n<=1` makes
`n==2` infeasible inside one lemma test (no disjunctive precondition). Both
files are identical except one assertion after `unfold Choice(#n)`:
the else branch checks `#n==1i` in `mixed-positive.gil` and `#n==0i` in
`mixed-error.gil`. Lemma postcondition and the `answer` procedure are
identical. The negative case therefore returns a list of outcomes containing,
simultaneously: a surviving proof state, an ordinary EPure assertion error
('Assert failed with argument'), and the checked `EInfeasibleUnfold` marker
from the infeasible `n==2` clause. Filtering ALL errors would wrongly accept
it; a pure error-only result would not catch the bug because the
empty-outcome guard rejects that case anyway.

## Expectations

- mixed-positive: rc 0; named `CheckChoice` lemma/answer/all-total success;
  2 symbolic tests; verbose `EInfeasibleUnfold` marker plus surviving proof
  branch (`LCMDs done with state:`); NO failed assertion, NO hard diagnostic.
- mixed-error: nonzero rc (124 is an expected Gillian rejection, not a
  timeout); named `CheckChoice` Failure; verbose ordinary
  'Assert failed with argument' AND surviving `LCMDs done with state:` AND
  `EInfeasibleUnfold`/unfold/nonadmissible markers; 2 symbolic tests; NO
  named success; downstream missing-checked-lemma rejection allowed.
  Timeout/crash/parser/import/terminal-SMT-unknown do not pass.
- Both: source/staged/executed hashes unchanged; raw producer records written
  before analysis; complete retained inventory. Raw proofAccepted /
  certificationReady / fullProofDone fields stay false; focused control review
  is recorded separately below.

## Evidence path

E=`/tmp/hermes-unfold-mixed-errors-p071`. Authoritative receipts:
`E/driver-producer.json`, `E/run-1/results/<case>/producer.json`, plus
`E/launch-result.json`. Per-case raw logs/queries/JSON are retained under
`E/run-1/`. Completed verbose logs are compressed with decoded-hash mappings;
all other raw receipts remain unchanged.

## Independent review

Card `t_060c1e96` is accepted as focused regression evidence. The positive
returned 0 with two surviving lemma branches; the negative returned 124 with
one surviving branch, the ordinary assertion error, and the checked infeasibility
marker. All 22 pins, 2,275 input files, 47 links and 34 output files were verified.
The two GIL files differ at exactly one checked assertion. No producer was rerun;
original reports remain immutable. Review and decoded-hash compression mappings:
`/tmp/hermes-unfold-mixed-errors-p071/independent-review.json` and
`compression-manifest.json`.

This does not close unexplained state-loss/simplification checks, affected backend
regression families, backend integration, or the full-fold theorem.
