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
    ("heap-alias-set.gil", ["--total"], TOTAL),
    ("heap-alias-set-wrong.gil", ["--total"], POST),
    ("heap-alias-delete.gil", ["--total"], TOTAL),
    ("heap-alias-delete-wrong.gil", ["--total"], POST),
    ("heap-alias-set-unproven.gil", ["--total"], (124, "requires an exposed property cell")),
    ("heap-alias-delete-unproven.gil", ["--total"], (124, "requires an exposed property cell")),
    ("return.gil", ["--total"], TOTAL),
    ("javascript-return.js", ["--total", "--proc=answer"], TOTAL),
    ("javascript-empty.js", ["--total", "--proc=answer"], TOTAL),
    ("heap-roundtrip.gil", ["--total"], TOTAL),
    ("heap-wrong-result.gil", ["--total"], POST),
    ("heap-list-no-progress.gil", ["--total"], DESCENT),
    ("heap-symbolic-key-wrong.gil", ["--total"], POST),
    ("heap-list.gil", ["--total"], TOTAL),
    ("heap-symbolic-key.gil", ["--total"], TOTAL),
    ("heap-missing.gil", ["--total"], (1, 'MIFCell(#obj, "missing")')),
    ("heap-branch-error.gil", ["--total"], (1, 'MIFCell(#obj, "missing")')),
    ("heap-unowned-write.gil", ["--total"], (124, "requires an exposed property cell")),
    ("heap-unowned-write.gil", [], PARTIAL),
    ("heap-unowned-delete.gil", ["--total"], (124, "requires an exposed property cell")),
    ("heap-partial-delete.gil", ["--total"], (124, "requires a complete object footprint")),
    ("heap-invalid-key.gil", ["--total"], (124, "requires a string property key")),
    ("heap-invalid-key.gil", [], PARTIAL),
    ("heap-fixed-allocation.gil", ["--total"], (124, "requires fresh allocation")),
    ("heap-delete-cell.gil", ["--total"], TOTAL),
    ("action-arity.gil", ["--total"], (124, "uncertified primitive action: Alloc/1")),
    ("logical-action.gil", ["--total"], (124, "uncertified primitive action: SetMetadata/2")),
    ("throw.gil", ["--total"], TOTAL),
    ("countdown.gil", ["--total"], TOTAL),
    ("decrement-before-call.gil", ["--total"], TOTAL),
    ("mutated-entry.gil", ["--total"], DESCENT),
    ("list.gil", ["--total"], TOTAL),
    ("list-no-progress.gil", ["--total"], DESCENT),
    ("list-no-progress.gil", [], PARTIAL),
    ("no-progress.gil", ["--total"], DESCENT),
    ("no-progress.gil", [], PARTIAL),
    ("increasing.gil", ["--total"], DESCENT),
    ("constant-rank.gil", ["--total"], DESCENT),
    ("negative-rank.gil", ["--total"], ENTRY),
    ("number-rank.gil", ["--total"], ENTRY),
    ("unbounded-below.gil", ["--total"], ENTRY),
    ("negative-call.gil", ["--total"], DESCENT),
    ("missing-rank.gil", ["--total"], (124, "needs a recursive-call variant")),
    ("ghost-rank.gil", ["--total"], (124, "variant must use only formal program parameters")),
    ("wrong-result.gil", ["--total"], POST),
    ("false-post.gil", ["--total"], POST),
    ("caller.gil", ["--total"], TOTAL),
    ("caller.gil", ["--total", "--proc=answer"], (124, "must be selected and proved total")),
    ("failed-callee.gil", ["--total"], (124, "has not passed every totality proof case")),
    ("loop.gil", ["--total"], (124, "has a control-flow cycle")),
    ("mutual.gil", ["--total"], (124, "mutually recursive procedures")),
    ("assume.gil", ["--total"], (124, "operation outside the totality fragment")),
    ("assume.gil", [], PARTIAL),
    ("invariant.gil", ["--total"], (124, "operation outside the totality fragment")),
    ("external.gil", ["--total"], (124, "operation outside the totality fragment")),
    ("action.gil", ["--total"], (124, "uncertified primitive action: unknown/0")),
    ("apply.gil", ["--total"], (124, "operation outside the totality fragment")),
    ("dynamic-call.gil", ["--total"], TOTAL),
    ("extra-argument.gil", ["--total"], (124, "requires exact call arity")),
    ("incomplete-spec.gil", ["--total"], (124, "requires a complete specification")),
    ("budget.gil", ["--total"], (124, "exploration budget exhausted")),
    ("budget.gil", [], PARTIAL),
    ("trusted-spec.gil", ["--total"], (124, "requires a complete specification")),
    ("split-callee.gil", ["--total"], TOTAL),
    ("failed-split-callee.gil", ["--total"], (124, "has not passed every totality proof case")),
    ("multiple-ranks.gil", ["--total"], (124, "same variant in every specification case")),
    ("duplicate-params.gil", ["--total"], (124, "duplicate formal parameters")),
    ("nonreturn.gil", ["--total"], (124, "edge outside its body")),
    ("empty-pre.gil", ["--total", "--no-unfold"], (124, "precondition")),
    ("false-post.gil", [], POST),
    ("return.gil", ["--total", "--incremental"], (124, "incremental verification cannot reuse")),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-procedure-totality-",
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
