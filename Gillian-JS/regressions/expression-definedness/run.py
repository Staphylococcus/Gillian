#!/usr/bin/env python3
"""Require the intended totality result; crashes and timeouts never pass."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get("GILLIAN_JS", "gillian-js"))
TOTAL = (0, "All total procedure specs succeeded")
PARTIAL = (0, "All specs succeeded")
DESCENT = (1, "variant is not a strictly smaller natural integer")
ENTRY = (1, "entry variant is not a natural integer")
POST = (1, "Couldn't satisfy postcondition")
CLOSED_PREDICATE = (124, "closed entry cannot abstract or assume heap resources")
CASES = [
    ("bitand-code-unit-required.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("bitand-code-unit-proof-required.gil", ["--total"], (1, "Pure assertion is not proved defined")),
    ("bitand-code-unit-valid.gil", ["--total"], TOTAL),
    ("bitand-untyped.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("bitand-wrong-type.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("bitand-required-child.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("bitand-proof-required.gil", ["--total"], (1, "Pure assertion is not proved defined")),
    ("bitand-proof-skipped.gil", ["--total"], TOTAL),
    ("bitand-proof-valid.gil", ["--total"], TOTAL),
    ("proof-matching-two-heads.gil", ["--total"], TOTAL),
    ("proof-matching-two-heads-wrong.gil", ["--total"], (1, "Pure assertion failed:")),
    ("proof-matching-two-heads-short.gil", ["--total"], (1, "Pure assertion failed:")),
    ("proof-matching-authored-tail-slice.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-tail-witness.gil", ["--total"], TOTAL),
    ("proof-matching-tail-wrong.gil", ["--total"], (1, "Pure assertion failed:")),
    ("proof-matching-resource-witness.gil", ["--total"], TOTAL),
    ("proof-matching-resource-wrong.gil", ["--total"], (1, "Assertion failed:")),
    ("proof-matching-whole-list-wrong.gil", ["--total"], (1, "Pure assertion failed:")),
    ("proof-matching-fold-body-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-fold-body-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-unfold-body-arbitrary.gil", ["--total"], (1, "Produced assertion is not proved defined")),
    ("proof-matching-unfold-body-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-whole-list-witness.gil", ["--total"], TOTAL),
    ("proof-matching-pre-false-branch.gil", ["--total"], (1, "Produced assertion is not proved defined")),
    ("proof-matching-post-skipped-witness.gil", ["--total"], TOTAL),
    ("proof-matching-forged-obligation.gil", ["--total"], (124, "internal definedness obligations in input assertions")),
    ("proof-matching-pre-arbitrary.gil", ["--total"], (1, "Produced assertion is not proved defined")),
    ("proof-matching-pre-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-post-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-post-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-sep-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-sep-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-binder-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-binder-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-auto-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-auto-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-unused-argument-arbitrary.gil", ["--total"], (1, "Matched assertion is not proved defined")),
    ("proof-matching-unused-argument-nonempty.gil", ["--total"], TOTAL),
    ("proof-matching-post-arbitrary.gil", [], PARTIAL),
    ("proof-predicate-fold-set-arbitrary.gil", ["--total"], (1, "Fold argument is not proved defined")),
    ("proof-predicate-fold-set-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-set-arbitrary.gil", ["--total"], (1, "Unfold argument is not proved defined")),
    ("proof-predicate-unfold-set-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-set-arbitrary.gil", ["--total"], (1, "Fold binding is not proved defined")),
    ("proof-predicate-binding-set-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-program-arbitrary.gil", ["--total"], (1, "Fold argument is not proved defined")),
    ("proof-predicate-fold-program-arbitrary.gil", [], PARTIAL),
    ("proof-predicate-fold-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-logical-arbitrary.gil", ["--total"], (1, "Fold argument is not proved defined")),
    ("proof-predicate-fold-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-guarded.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-path-guard.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-closed-empty.gil", ["--total"], (1, "Fold argument is not proved defined")),
    ("proof-predicate-fold-closed-empty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-fold-closed-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-fold-closed-nonempty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-fold-branch-local.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-program-arbitrary.gil", ["--total"], (1, "Unfold argument is not proved defined")),
    ("proof-predicate-unfold-program-arbitrary.gil", [], PARTIAL),
    ("proof-predicate-unfold-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-logical-arbitrary.gil", ["--total"], (1, "Unfold argument is not proved defined")),
    ("proof-predicate-unfold-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-guarded.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-path-guard.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-closed-empty.gil", ["--total"], (1, "Unfold argument is not proved defined")),
    ("proof-predicate-unfold-closed-empty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-unfold-closed-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-unfold-closed-nonempty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-unfold-branch-local.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-program-arbitrary.gil", ["--total"], (1, "Fold binding is not proved defined")),
    ("proof-predicate-binding-program-arbitrary.gil", [], PARTIAL),
    ("proof-predicate-binding-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-logical-arbitrary.gil", ["--total"], (1, "Fold binding is not proved defined")),
    ("proof-predicate-binding-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-guarded.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-path-guard.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-closed-empty.gil", ["--total"], (1, "Fold binding is not proved defined")),
    ("proof-predicate-binding-closed-empty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-binding-closed-nonempty.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-closed-nonempty.gil", ["--total", "--closed-entry", "--proc=main"], CLOSED_PREDICATE),
    ("proof-predicate-binding-branch-local.gil", ["--total"], TOTAL),
    ("proof-predicate-binding-wrong-value.gil", ["--total"], (1, "Assertion failed:")),
    ("proof-predicate-rec-unfold-arbitrary.gil", ["--total"], (1, "Unfold argument is not proved defined")),
    ("proof-predicate-rec-unfold-nonempty.gil", ["--total"], TOTAL),
    ("proof-normalize-length-required.gil", ["--total"], (1, "Assertion reduction failed")),
    ("proof-normalize-length-required.gil", ["--total", "--closed-entry", "--proc=main"], (1, "Assertion reduction failed")),
    ("proof-normalize-length-skipped.gil", ["--total"], TOTAL),
    ("proof-normalize-length-skipped.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-normalize-length-valid.gil", ["--total"], TOTAL),
    ("proof-normalize-length-valid.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-normalize-identity-required.gil", ["--total"], (1, "Assertion reduction failed")),
    ("proof-normalize-identity-required.gil", ["--total", "--closed-entry", "--proc=main"], (1, "Assertion reduction failed")),
    ("proof-normalize-identity-skipped.gil", ["--total"], TOTAL),
    ("proof-normalize-identity-skipped.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-normalize-identity-valid.gil", ["--total"], TOTAL),
    ("proof-normalize-identity-valid.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-assert-branch-local-skipped.gil", ["--total"], TOTAL),
    ("proof-assert-branch-local-required.gil", ["--total"], (1, "Undefined variable: x")),
    ("proof-condition-branch-local-skipped.gil", ["--total"], TOTAL),
    ("proof-condition-branch-local-required.gil", ["--total"], (1, "Undefined variable: x")),
    ("proof-assert-branch-local-skipped.gil", [], PARTIAL),
    ("proof-assert-program-arbitrary.gil", ["--total"], (1, "Pure assertion is not proved defined")),
    ("proof-assert-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-assert-logical-arbitrary.gil", ["--total"], (1, "Pure assertion is not proved defined")),
    ("proof-assert-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-assert-guarded.gil", ["--total"], TOTAL),
    ("proof-assert-program-arbitrary.gil", [], PARTIAL),
    ("proof-assert-closed-empty.gil", ["--total"], (1, "Pure assertion is not proved defined")),
    ("proof-assert-closed-empty.gil", ["--total", "--closed-entry", "--proc=main"], (1, "Pure assertion is not proved defined")),
    ("proof-assert-closed-nonempty.gil", ["--total"], TOTAL),
    ("proof-assert-closed-nonempty.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-condition-program-arbitrary.gil", ["--total"], (1, "Logical condition is not proved defined")),
    ("proof-condition-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-condition-logical-arbitrary.gil", ["--total"], (1, "Logical condition is not proved defined")),
    ("proof-condition-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-condition-guarded.gil", ["--total"], TOTAL),
    ("proof-condition-program-arbitrary.gil", [], PARTIAL),
    ("proof-condition-closed-empty.gil", ["--total"], (1, "Logical condition is not proved defined")),
    ("proof-condition-closed-empty.gil", ["--total", "--closed-entry", "--proc=main"], (1, "Logical condition is not proved defined")),
    ("proof-condition-closed-nonempty.gil", ["--total"], TOTAL),
    ("proof-condition-closed-nonempty.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("proof-condition-path-guard.gil", ["--total"], TOTAL),
    ("proof-condition-sibling-failure.gil", ["--total"], (1, "Pure assertion failed")),
    ("proof-substitution-program-arbitrary.gil", ["--total"], (1, "Summary substitution is not proved defined")),
    ("proof-substitution-logical-arbitrary.gil", ["--total"], (1, "Summary substitution is not proved defined")),
    ("proof-substitution-program-nonempty.gil", ["--total"], TOTAL),
    ("proof-substitution-logical-nonempty.gil", ["--total"], TOTAL),
    ("proof-substitution-short-circuit.gil", ["--total"], TOTAL),
    ("proof-substitution-required.gil", ["--total"], (1, "Summary substitution is not proved defined")),
    ("proof-substitution-program-arbitrary.gil", [], PARTIAL),
    ("proof-procedure-rank-arbitrary.gil", ["--total"], (1, "Entry variant is not proved defined")),
    ("proof-procedure-rank-nonempty.gil", ["--total"], TOTAL),
    ("proof-procedure-rank-call.gil", ["--total"], (1, "Procedure recursive variant is not proved defined")),
    ("proof-loop-rank-arbitrary.gil", ["--total"], (1, "Loop entry variant is not proved defined")),
    ("proof-loop-rank-generalized.gil", ["--total"], (1, "Loop entry variant is not proved defined")),
    ("proof-loop-rank-nonempty.gil", ["--total"], TOTAL),
    ("proof-lemma-rank-arbitrary.gil", ["--total"], (1, "Entry variant is not proved defined")),
    ("proof-lemma-rank-nonempty.gil", ["--total"], TOTAL),
    ("proof-lemma-rank-call.gil", ["--total"], (1, "Lemma recursive variant is not proved defined")),
    ("proof-lemma-argument.gil", ["--total"], (1, "Lemma argument is not proved defined")),
    ("proof-lemma-argument-nonempty.gil", ["--total"], TOTAL),
    ("proof-boolean-branch.gil", ["--total"], (1, "Pure assertion failed")),
    ("proof-boolean-branch.gil", ["--total", "--closed-entry", "--proc=main"], (1, "Pure assertion failed")),
    ("proof-boolean-post.gil", ["--total"], POST),
    ("proof-boolean-post.gil", ["--total", "--closed-entry", "--proc=main"], POST),
    ("proof-boolean-short-circuit.gil", ["--total"], TOTAL),
    ("proof-boolean-short-circuit.gil", ["--total", "--closed-entry", "--proc=main"], (0, "Closed entry postcondition succeeded")),
    ("symbolic-conversion-infinite.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("symbolic-conversion-nan.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("symbolic-index-past-end.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("symbolic-index-wrong.gil", ["--total"], POST),
    ("symbolic-index.gil", ["--total"], TOTAL),
    ("integer-division.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("integer-modulo.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("untyped-addition.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("untyped-bytes.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("string-index.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("bad-boolean-operand.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("nonfinite-conversion.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("integer-division-nonzero.gil", ["--total"], TOTAL),
    ("signed-division-correct.gil", ["--total"], TOTAL),
    ("signed-remainder-correct.gil", ["--total"], TOTAL),
    ("string-index-nonempty.gil", ["--total"], TOTAL),
    ("float-division.gil", ["--total"], TOTAL),
    ("skipped-boolean-operand.gil", ["--total"], TOTAL),
    ("finite-conversion.gil", ["--total"], TOTAL),
    ("signed-division.gil", ["--total"], POST),
    ("signed-remainder.gil", ["--total"], POST),
    ("untyped-read.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("unused-read.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("guarded-read.gil", ["--total"], TOTAL),
    ("nonempty-read.gil", ["--total"], TOTAL),
    ("unused-tail.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("unused-head.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("negative-index.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("one-past-end.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("short-circuit.gil", ["--total"], TOTAL),
    ("evaluated-operand.gil", ["--total"], (1, "Executed operation is not proved defined")),
    ("hidden-in-identity.gil", ["--total"], (1, "Executed operation is not proved defined")),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-expression-definedness-",
                                  dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for index, (file, options, expected) in enumerate(CASES):
        source = ROOT / file
        directory = output / f"{index:02d}-{source.stem}"
        directory.mkdir()
        command = COMMAND + ["verify", str(source), "--logging=normal"] + (["-a"] if source.suffix == ".gil" else []) + options
        record = {"file": file, "command": command, "expectedExit": expected[0],
                  "expectedMessage": expected[1],
                  "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest()}
        try:
            run = subprocess.run(command, cwd=directory, capture_output=True,
                                 text=True, errors="replace", timeout=45)
            text = run.stdout + run.stderr
            (directory / "output.log").write_text(text)
            passed = run.returncode == expected[0] and expected[1] in text
            if expected[0] != 0:
                passed &= "All total procedure specs succeeded" not in text
            record |= {"passed": passed, "exitCode": run.returncode, "output": text}
        except subprocess.TimeoutExpired:
            record |= {"passed": False, "reason": "timeout"}
        results.append(record)
        print(f"{file} {options}: {'PASS' if record['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(r["passed"] for r in results) else 1)
