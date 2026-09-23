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
