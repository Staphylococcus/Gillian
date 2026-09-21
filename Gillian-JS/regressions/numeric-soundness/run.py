#!/usr/bin/env python3
"""Run semantic controls; crashes, timeouts and incomplete paths never pass."""

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
    ("number-rounding", "wpst", None, True),
    ("number-symbolic-monotonic", "wpst", None, False),
    ("deductive-number-monotonic", "verify", "increment", False),
    ("deductive-number-step-two", "verify", "incrementTwo", True),
    ("number-overflow-nan", "wpst", None, True),
    ("number-signed-zero", "wpst", None, True),
    ("number-signed-zero-fail", "wpst", None, False),
    ("heap-alias", "wpst", None, True),
]


def run_case(name, mode, proc, expected_success, output):
    source = ROOT / (name + ".js")
    case_dir = output / name
    case_dir.mkdir()
    command = COMMAND + [mode, str(source), "--logging=normal"]
    if mode == "wpst":
        command += ["--json-ui", "--unroll=100"]
    if proc:
        command += ["--proc", proc]
    result = {
        "case": name, "command": command,
        "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "expectedSuccess": expected_success,
    }
    try:
        execution = subprocess.run(command, cwd=case_dir, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   timeout=60, check=False)
    except subprocess.TimeoutExpired:
        return result | {"passed": False, "reason": "timeout"}
    text = execution.stdout
    (case_dir / "output.log").write_text(text)
    log = case_dir / "file.log"
    incomplete = any(marker in (log.read_text() if log.exists() else "")
                     for marker in ("MAX BRANCHING", "Stopping Symbolic Execution"))
    result.update(exitCode=execution.returncode, incomplete=incomplete)
    if mode == "wpst":
        try:
            payload = text.split("===JSON RESULTS===", 1)[1].lstrip()
            paths, _ = json.JSONDecoder().raw_decode(payload)
        except (IndexError, ValueError):
            return result | {"passed": False, "reason": "missing path results"}
        failures = [p for p in paths if p[0] == "RFail"]
        normal = [p for p in paths if p[0] == "RSucc"
                  and p[1]["flag"] == ["Normal"]]
        assertion_errors = all(
            len(p[1]["errors"]) == 1
            and p[1]["errors"][0][0] == "EState"
            and p[1]["errors"][0][1][0] == "EPure"
            and p[1]["loc"]["loc_start"]["pos_line"]
                == next(i for i, line in enumerate(source.read_text().splitlines(), 1)
                        if line.startswith("Assert("))
            for p in failures
        )
        if expected_success:
            passed = execution.returncode == 0 and len(normal) == len(paths) > 0
        else:
            passed = (execution.returncode == 1 and bool(failures) and assertion_errors
                      and len(normal) + len(failures) == len(paths))
        result.update(pathCount=len(paths), failedPaths=len(failures))
    elif expected_success:
        passed = execution.returncode == 0 and "All specs succeeded" in text
    else:
        passed = execution.returncode == 1 and "Couldn't satisfy postcondition" in text
    return result | {"passed": passed and not incomplete}


if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-numeric-"))
    results = []
    for case in CASES:
        result = run_case(*case, output)
        results.append(result)
        print(f"{case[0]}: {'PASS' if result['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(result["passed"] for result in results) else 1)
