#!/usr/bin/env python3
"""Check actual compiled JS loop obligations; unrelated errors never pass."""
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
PRESERVE = (1, "Loop invariant preservation failed")
CASES = [
    ("broken-backedge.js", [], PRESERVE),
    ("broken-backedge-correct-post.js", [], PRESERVE),
    ("mixed-exit.js", [], PRESERVE),
    ("nested-broken.js", [], PRESERVE),
    ("broken-entry.js", [], (1, "Loop invariant establishment failed")),
    ("valid-loop.js", [], SUCCESS),
    ("zero-iterations.js", [], SUCCESS),
    ("framed-local.js", [], SUCCESS),
    ("break-loop.js", [], SUCCESS),
    ("return-loop.js", [], SUCCESS),
    ("throw-loop.js", [], SUCCESS),
    ("nested-loop.js", [], SUCCESS),
    ("wrong-post.js", [], (1, "Couldn't satisfy postcondition")),
    ("unannotated-invariant.gil", ["-a"], (124, "Loop invariant requires loop metadata")),
    # Successful invariant checks still prove only partial correctness.
    ("forever.js", [], SUCCESS),
    ("forever.js", ["--total"], (124, "has a control-flow cycle")),
    ("valid-loop.js", ["--total"], (124, "has a control-flow cycle")),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-loop-soundness-",
                                  dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for index, (file, options, expected) in enumerate(CASES):
        source = ROOT / file
        directory = output / f"{index:02d}-{source.stem}"
        directory.mkdir()
        command = COMMAND + ["verify", str(source), "--proc=check", "--logging=normal"] + options
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
                passed &= "All specs succeeded" not in text and "All total procedure specs succeeded" not in text
            record |= {"passed": passed, "exitCode": run.returncode, "output": text}
        except subprocess.TimeoutExpired:
            record |= {"passed": False, "reason": "timeout"}
        results.append(record)
        print(f"{file} {options}: {'PASS' if record['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(r["passed"] for r in results) else 1)
