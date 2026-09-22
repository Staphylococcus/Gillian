#!/usr/bin/env python3
"""Concrete execution controls, including ordinary thrown-error exit status."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get("GILLIAN_JS", "gillian-js"))
CASES = [
    ("call.js", 0, 'SUCCESSFUL TERMINATION: (normal, "concrete call ready")'),
    ("nested-call.js", 0, 'SUCCESSFUL TERMINATION: (normal, "nested call ready")'),
    ("loop-call.js", 0, 'SUCCESSFUL TERMINATION: (normal, "loop call ready")'),
    ("caught-call.js", 0, 'SUCCESSFUL TERMINATION: (normal, "caught call ready")'),
    ("empty-call.js", 0, 'SUCCESSFUL TERMINATION: (normal, "empty call ready")'),
    ("call-wrong.js", 1, 'SUCCESSFUL TERMINATION: (error,'),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-concrete-execution-", dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for file, expected, marker in CASES:
        source = ROOT / file
        directory = output / source.stem
        directory.mkdir()
        command = COMMAND + ["exec", str(source), "--print-final-state", "--no-heap", "--logging=normal"]
        record = {"file": file, "command": command, "expectedExit": expected, "expectedMessage": marker,
                  "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest()}
        try:
            run = subprocess.run(command, cwd=directory, capture_output=True, text=True, timeout=45)
            text = run.stdout + run.stderr
            (directory / "output.log").write_text(text)
            passed = run.returncode == expected and marker in text and "internal error" not in text
            record |= {"passed": passed, "exitCode": run.returncode, "output": text}
        except subprocess.TimeoutExpired:
            record |= {"passed": False, "reason": "timeout"}
        results.append(record)
        print(f"{file}: {'PASS' if record['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(r["passed"] for r in results) else 1)
