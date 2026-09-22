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
    ("logical-binder.gil", ["--total"], TOTAL),
    ("shadow-caller-identity.gil", ["--total", "--proc=count"], (124, "logical invariant binders shadow protected")),
    ("nested-inner-stuck.gil", ["--total"], DESCENT),
    ("nested-outer-stuck.gil", ["--total"], DESCENT),
    ("nested-outer-increase.gil", ["--total"], DESCENT),
    ("nested-wrong-post.gil", ["--total"], POST),
    ("nested-omitted-parent.gil", ["--total"], (1, "Executed operation is not proved defined: (n i+ 1i)")),
    ("sequential-adjacent.gil", ["--total"], TOTAL),
    ("sequential-stuck.gil", ["--total"], DESCENT),
    ("nested-break.gil", ["--total"], TOTAL),
    ("nested-three.gil", ["--total"], TOTAL),
    ("nested-framed-heap.gil", ["--total"], TOTAL),
    ("nested-break-heap.gil", ["--total"], TOTAL),
    ("nested-helper.gil", ["--total", "--proc=count"], TOTAL),
    ("omitted-helper-result.gil", ["--total", "--proc=count"], (1, "Executed operation is not proved defined: (x i+ 1i)")),
    ("macro-live-local.gil", ["--total"], (1, "Pure assertion failed")),
    ("unbound-counter.gil", ["--total"], TOTAL),
    ("omitted-live-local.gil", ["--total"], (1, "Executed operation is not proved defined: (acc i+ 1i)")),
    ("unbound-live-local.gil", ["--total"], POST),
    ("captured-live-local.gil", ["--total"], TOTAL),
    ("captured-local-wrong-post.gil", ["--total"], POST),
    ("dead-temporary.gil", ["--total"], TOTAL),
    ("zero-entry.gil", ["--total"], TOTAL),
    ("entry-five-stuck-one.gil", ["--total"], DESCENT),
    ("negative-back-edge.gil", ["--total"], (1, "Loop invariant preservation failed")),
    ("return-from-loop.gil", ["--total"], TOTAL),
    ("wrong-early-return.gil", ["--total"], POST),
    ("invariant-outside.gil", ["--total"], (124, "operation outside the totality fragment")),
    ("nested.gil", ["--total"], TOTAL),
    ("sequential.gil", ["--total"], TOTAL),
    ("framed-heap.gil", ["--total"], TOTAL),
    ("proved-callee.gil", ["--total"], TOTAL),
    ("failed-callee.gil", ["--total"], (124, "has not passed every totality proof case")),

    ("countdown.gil", ["--total"], TOTAL),
    ("list.gil", ["--total"], TOTAL),
    ("multiple-back-edges.gil", ["--total"], TOTAL),
    ("break.gil", ["--total"], TOTAL),
    ("no-progress.gil", ["--total"], DESCENT),
    ("increasing.gil", ["--total"], DESCENT),
    ("constant-rank.gil", ["--total"], DESCENT),
    ("list-no-progress.gil", ["--total"], DESCENT),
    ("negative-rank.gil", ["--total"], ENTRY),
    ("number-rank.gil", ["--total"], DESCENT),
    ("weak-invariant.gil", ["--total"], ENTRY),
    ("wrong-post.gil", ["--total"], POST),
    ("bad-preservation.gil", ["--total"], (1, "Loop invariant preservation failed")),
    ("ghost-rank.gil", ["--total"], (124, "loop variant must use only program variables")),
    ("uncaptured-rank.gil", ["--total"], (124, "loop variant must use only program variables")),
    ("missing-rank.gil", ["--total"], (124, "without a ranked invariant header")),
    ("first-iteration-only.gil", ["--total"], DESCENT),
    ("branch-no-progress.gil", ["--total"], DESCENT),
    ("bypass-entry.gil", ["--total"], (124, "entry bypassing its ranked header")),
    ("bypass-cycle.gil", ["--total"], (124, "without a ranked invariant header")),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-loop-totality-",
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
