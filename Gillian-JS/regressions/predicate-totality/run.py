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
    ("nounfold-demand.gil", ["--total"], TOTAL),
    ("nounfold-demand-wrong.gil", ["--total"], POST),
    ("fabricated-cell.gil", ["--total"], (1, "MIFCell(#obj, \"x\")")),
    ("empty-subset-wrong.gil", ["--total"], POST),
    ("empty-subset.gil", ["--total"], TOTAL),
    ("domain-unknown-difference.gil", ["--total"], (124, "Unsupported property-domain matching")),
    ("domain-present-shrink.gil", ["--total"], POST),
    ("domain-unknown-shrink.gil", ["--total"], POST),
    ("domain-absent-shrink.gil", ["--total"], TOTAL),
    ("domain-grow.gil", ["--total"], TOTAL),
    ("domain-symbolic-negative.gil", ["--total"], TOTAL),
    ("unfold-budget.gil", ["--total"], (124, "recursive predicate unfolding exhausted its proof budget")),
    ("facts-identity.gil", ["--total"], TOTAL),
    ("false-facts-auto.gil", ["--total"], POST),
    ("false-facts-auto.gil", ["--total", "--no-unfold"], POST),
    ("transitive-purity.gil", ["--total"], POST),
    ("heap-cell.gil", ["--total"], TOTAL),
    ("heap-wrong.gil", ["--total"], POST),
    ("false-facts.gil", ["--total"], POST),
    ("false-facts-pre.gil", ["--total"], POST),
    ("pure-heap.gil", ["--total"], POST),
    ("global-unfold.gil", ["--total"], TOTAL),
    ("false-unfold-branch.gil", ["--total"], POST),
    ("pure-choice.gil", ["--total"], TOTAL),
    ("fold-false.gil", ["--total"], (1, "Assertion failed: (0i == 1i)")),
    ("guarded.gil", ["--total"], (124, "guarded predicate")),
    ("inductive-count.gil", ["--total"], TOTAL),
    ("inductive-no-progress.gil", ["--total"], (124, "has not passed every lemma proof case")),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-predicate-totality-",
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
