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
    ("forward-length-measure.gil", ["--total"], (124, "Incomplete totality proof: SMT returned unknown")),
    ("forward-no-progress.gil", ["--total"], DESCENT),
    ("forward-wrong-post.gil", ["--total"], POST),
    ("integer-bridge-unresolved.gil", ["--total"], (124, "Incomplete totality proof: SMT returned unknown")),
    ("countdown.gil", ["--total"], TOTAL),
    ("exact-bound.gil", ["--total"], TOTAL),
    ("rounding-stall.gil", ["--total"], DESCENT),
    ("no-progress.gil", ["--total"], DESCENT),
    ("increasing.gil", ["--total"], (1, [DESCENT[1], "Loop invariant preservation failed"])),
    ("fractional.gil", ["--total"], ENTRY),
    ("negative.gil", ["--total"], ENTRY),
    ("infinite.gil", ["--total"], ENTRY),
    ("nan.gil", ["--total"], ENTRY),
    ("wrong-post.gil", ["--total"], POST),
    ("changed-type.gil", ["--total"], (1, "Loop invariant preservation failed")),
    ("signed-zero.gil", ["--total"], TOTAL),
    ("forward.gil", ["--total"], TOTAL),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-number-loop-totality-",
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
            messages = [expected[1]] if isinstance(expected[1], str) else expected[1]
            passed = run.returncode == expected[0] and any(message in text for message in messages)
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
