#!/usr/bin/env python3
"""Character-code controls: only completed normal paths count as success."""
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
    ("concrete", "normal", 100),
    ("coercion", "normal", 100),
    ("loop-exception", "normal", 100),
    ("ordering", "normal", 100),
    ("operations", "normal", 100),
    ("construction-coercion", "normal", 100),
    ("literal-values", "normal", 100),
    ("generated-code", "normal", 100),
    ("symbolic-choice", "normal", 100),
    ("wrong-code-point", "assertion", 100),
    ("symbolic-string", "unsupported", 100),
    ("generated-lone-source", "unsupported", 100),
    ("concrete", "cutoff", 0),
]


def run_case(name, expectation, budget, output):
    source = ROOT / (name + ".js")
    directory = output / (name + "-" + expectation)
    directory.mkdir()
    command = COMMAND + ["wpst", str(source), "--logging=normal", "--no-heap",
                         "--json-ui", f"--unroll={budget}"]
    record = {"case": name, "expectation": expectation, "command": command,
              "sourceSha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    try:
        process = subprocess.run(command, cwd=directory, capture_output=True,
                                 text=True, errors="replace", timeout=60)
    except subprocess.TimeoutExpired:
        return record | {"passed": False, "reason": "timeout"}
    text = process.stdout + process.stderr
    (directory / "output.log").write_text(text)
    log = directory / "file.log"
    cutoff = any(marker in (log.read_text(errors="replace") if log.exists() else "")
                 for marker in ("MAX BRANCHING", "Stopping Symbolic Execution"))
    paths = None
    if "===JSON RESULTS===" in process.stdout:
        paths, _ = json.JSONDecoder().raw_decode(
            process.stdout.split("===JSON RESULTS===", 1)[1].lstrip())
    normal = [p for p in paths or []
              if p[0] == "RSucc" and p[1]["flag"] == ["Normal"]]
    if expectation == "normal":
        passed = process.returncode == 0 and bool(paths) and len(normal) == len(paths)
        if name == "symbolic-choice":
            passed = passed and len(normal) == 2
    elif expectation == "assertion":
        passed = process.returncode == 1 and bool(paths) and all(
            p[0] == "RFail" and p[1]["proc"] == "main"
            and p[1]["errors"] == [["EState", ["EPure", ["Lit", ["Bool", False]]]]]
            and p[1]["loc"]["loc_start"]["pos_line"] == 4 for p in paths)
    elif expectation == "unsupported":
        passed = process.returncode != 0 and not normal and not cutoff and (
            any(message in text for message in ("ExecuteStringCodeUnits requires a concrete string", "ExecuteStringLength requires concrete operands", "Lone surrogate in generated JavaScript source")))
    else:
        passed = cutoff
    return record | {"passed": passed and (expectation == "cutoff" or not cutoff),
                     "exitCode": process.returncode, "cutoff": cutoff, "paths": paths}


if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-string-code-units-",
                                  dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for case in CASES:
        result = run_case(*case, output)
        results.append(result)
        print(f"{case[0]} ({case[1]}): {'PASS' if result['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(result["passed"] for result in results) else 1)
