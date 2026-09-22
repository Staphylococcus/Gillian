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
CASES = [
    ("identity-cons-zero-wrong.gil", ["--total"], POST),
    ("identity-cons-zero.gil", ["--total"], TOTAL),
    ("identity-cons-nan-wrong.gil", ["--total"], POST),
    ("identity-cons-nan.gil", ["--total"], TOTAL),
    ("identity-numeric-precondition.gil", ["--total", "--proc=answer"], POST),
    ("identity-exact-precondition.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-numeric-summary.gil", ["--total"], POST),
    ("identity-exact-summary.gil", ["--total"], TOTAL),
    ("number-countdown-wrong-zero.gil", ["--total"], POST),
    ("identity-cell-zero.gil", ["--total", "--proc=answer"], POST),
    ("identity-predicate-zero.gil", ["--total", "--proc=answer"], POST),
    ("identity-cell-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-predicate-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-symbolic-number.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-symbolic-predicate.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-numeric-zero-constraint.gil", ["--total", "--proc=answer"], POST),
    ("identity-nested-zero.gil", ["--total", "--proc=answer"], POST),
    ("identity-nested-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-wrong-number.gil", ["--total", "--proc=answer"], POST),
    ("identity-input-zero.gil", ["--total", "--proc=answer"], POST),
    ("identity-input-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-operator-zero.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-operator-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-numeric-zero.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-numeric-nan.gil", ["--total", "--proc=answer"], TOTAL),
    ("identity-predicate-zero.gil", ["--proc=answer"], POST),
    ("identity-number-segment.gil", ["--total", "--proc=answer", "--lemma=AppendNum"], TOTAL),
    ("shared-metadata-caller.gil", ["--total", "--proc=answer"], TOTAL),
    ("shared-metadata-caller-wrong.gil", ["--total", "--proc=answer"], POST),
    ("shared-metadata-nested.gil", ["--total"], TOTAL),
    ("shared-metadata-nested-wrong.gil", ["--total"], POST),
    ("shared-metadata.gil", ["--total"], TOTAL),
    ("shared-metadata-wrong.gil", ["--total"], POST),
    ("shared-metadata-stuck.gil", ["--total"], DESCENT),
    ("shared-metadata-frame.gil", ["--total"], TOTAL),
    ("shared-metadata-frame-wrong.gil", ["--total"], POST),
    ("shared-metadata-exclusive.gil", ["--total"], (1, "MIFCell")),
    ("shared-metadata-update.gil", ["--total"], TOTAL),
    ("shared-metadata-update-wrong.gil", ["--total"], POST),
    ("shared-metadata-update-stuck.gil", ["--total"], DESCENT),
    ("javascript-forward.js", ["--total", "--proc=count"], TOTAL),
    ("javascript-forward-stuck.js", ["--total", "--proc=count"], DESCENT),
    ("javascript-countdown.js", ["--total", "--proc=count"], TOTAL),
    ("javascript-stuck.js", ["--total", "--proc=count"], DESCENT),
    ("javascript-wrong.js", ["--total", "--proc=count"], POST),
    ("javascript-stuck-one.js", ["--total", "--proc=count"], DESCENT),
    ("javascript-for.js", ["--total", "--proc=count"], TOTAL),
    ("javascript-empty-loop.js", ["--total", "--proc=count"], DESCENT),
    ("phi-countdown.gil", ["--total"], TOTAL),
    ("phi-stuck.gil", ["--total"], DESCENT),
    ("phi-wrong.gil", ["--total"], POST),
    ("phi-missing-entry.gil", ["--total"], (1, "Undefined variable: missing")),
    ("phi-prefix-action.gil", ["--total"], (124, "entry bypassing its ranked header")),
    ("phi-sequential.gil", ["--total"], TOTAL),
    ("shadow-input.gil", ["--total"], (124, "logical invariant binders shadow protected")),
    ("list.gil", ["--total"], TOTAL),
    ("list-no-progress.gil", ["--total"], DESCENT),
    ("accumulator.gil", ["--total"], TOTAL),
    ("accumulator-wrong.gil", ["--total"], POST),
    ("countdown.gil", ["--total"], TOTAL),
    ("no-progress.gil", ["--total"], DESCENT),
    ("increasing.gil", ["--total"], DESCENT),
    ("wrong-post.gil", ["--total"], POST),
    ("stuck-one.gil", ["--total"], DESCENT),
    ("uncaptured-rank.gil", ["--total"], (124, "loop variant must use only program variables")),
    ("number-countdown.gil", ["--total"], TOTAL),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-heap-loop-totality-",
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
