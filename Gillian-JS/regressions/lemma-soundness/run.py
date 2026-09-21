#!/usr/bin/env python3
"""Check lemma rejection reasons; unrelated failures and timeouts never pass."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get("GILLIAN_JS", "gillian-js"))
SUCCESS = (0, "All specs succeeded")
FALSE_POST = (1, "Couldn't satisfy postcondition")
CYCLE = (124, "Unsupported recursive lemma proof dependency")
ENTRY = (1, "entry variant is not a natural integer")
DESCENT = (1, "variant is not a strictly smaller natural integer")
CASES = [
    ("return.js", ["--procs-only"], SUCCESS),
    ("wrong-return.js", ["--procs-only"], FALSE_POST),
    ("valid-lemmas.jsil", ["--jsil"], SUCCESS),
    ("mixed-posts.jsil", ["--jsil"], SUCCESS),
    ("invalid-lemma.jsil", ["--jsil"], FALSE_POST),
    ("false-post-lemma.jsil", ["--jsil"], FALSE_POST),
    ("false-post-substitution.jsil", ["--jsil"], FALSE_POST),
    ("circular-lemma.jsil", ["--jsil"], ENTRY),
    ("self-no-variant.jsil", ["--jsil"], CYCLE),
    ("mutual.jsil", ["--jsil"], CYCLE),
    ("macro-cycle.jsil", ["--jsil"], ENTRY),
    ("macro-self-cycle.jsil", ["--jsil"], CYCLE),
    ("circular-caller.js", ["--proc=answer", "--lemma=ForceTrue"], CYCLE),
    ("circular-caller.js", ["--procs-only"], CYCLE),
    ("unrelated-cycle.jsil", ["--jsil", "--proc=answer"], SUCCESS),
    ("countdown.gil", ["-a"], SUCCESS),
    ("induction.gil", ["-a"], SUCCESS),
    ("induction-missing-hypothesis.gil", ["-a"], (1, "Assertion failed")),
    ("induction-repeat-calls.gil", ["-a"], SUCCESS),
    ("induction-failed-caller.gil", ["-a"], CYCLE),
    ("induction-pvar.gil", ["-a"], SUCCESS),
    ("induction-list.gil", ["-a"], SUCCESS),
    ("induction-list-no-progress.gil", ["-a"], DESCENT),
    ("induction-no-progress.gil", ["-a"], DESCENT),
    ("induction-increase.gil", ["-a"], DESCENT),
    ("induction-constant.gil", ["-a"], DESCENT),
    ("induction-negative.gil", ["-a"], ENTRY),
    ("induction-noninteger.gil", ["-a"], ENTRY),
    ("induction-unbounded-below.gil", ["-a"], ENTRY),
    ("induction-negative-call.gil", ["-a"], DESCENT),
    ("induction-ghost-rank.gil", ["-a"], CYCLE),
    ("induction-false-base.gil", ["-a"], FALSE_POST),
    ("induction-false-split-base.gil", ["-a"], FALSE_POST),
    ("induction-macro.gil", ["-a"], SUCCESS),
    ("induction-macro-no-progress.gil", ["-a"], DESCENT),
    ("induction-macro-loop.gil", ["-a"], CYCLE),
    ("induction-caller.gil", ["-a"], SUCCESS),
    ("induction-caller.gil", ["-a", "--procs-only"], CYCLE),
    ("induction-caller.gil", ["-a", "--lemma=ACaller"], CYCLE),
    # These remain partial-correctness results, not totality certificates.
    ("chain.js", ["--procs-only"], SUCCESS),
    ("chain-no-progress.js", ["--procs-only"], SUCCESS),
    ("recursive.js", ["--procs-only"], SUCCESS),
    ("loop.js", ["--procs-only"], SUCCESS),
]


def run_case(index, file, options, expected, output):
    source = ROOT / file
    directory = output / f"{index:02d}-{source.stem}"
    directory.mkdir()
    command = COMMAND + ["verify", str(source), "--logging=normal"] + options
    record = {"file": file, "command": command, "expectedExit": expected[0],
              "expectedMessage": expected[1],
              "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    try:
        run = subprocess.run(command, cwd=directory, capture_output=True,
                             text=True, errors="replace", timeout=45)
    except subprocess.TimeoutExpired:
        return record | {"passed": False, "reason": "timeout"}
    text = run.stdout + run.stderr
    (directory / "output.log").write_text(text)
    passed = run.returncode == expected[0] and expected[1] in text
    if expected[0] != 0:
        passed = passed and "All specs succeeded" not in text
    return record | {"passed": passed, "exitCode": run.returncode,
                     "output": text}


if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-lemma-soundness-",
                                  dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for index, case in enumerate(CASES):
        result = run_case(index, *case, output)
        results.append(result)
        print(f"{case[0]} {case[1]}: {'PASS' if result['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(r["passed"] for r in results) else 1)
