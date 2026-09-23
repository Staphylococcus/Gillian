#!/usr/bin/env python3
"""P09 serializer controls: JSON.stringify through the actual pinned json3.js,
run on the reduced InitFantine init (JSON global registered) under wpst.

Covers the P09 serializer surface that P07 (object keys) / P08 (filter/callbacks)
do not:
  - nested object/array composition,
  - empty array/object,
  - control-character + quote + lone-surrogate escaping,
  - key order preservation,
  - number text, negative-zero (-0 -> "0"), extreme finite (5e-324), non-finite (NaN/Inf -> "null").

Each fixture embeds the pinned JSON3 model (json3.js) at the top so the bare
fixture is self-contained: the suite's install runtime (-R) does not ship the
JSON runtime, so run.py passes the bare fixture path (no inlining) and the
catalogue's sourceSha256 of the bare file equals the executed source.

Node oracle (JSON.stringify):
  {a:[1,-0]}   -> '{"a":[1,0]}'
  [] -> "[]"   {} -> "{}"
  -0 -> "0"    NaN/Inf/-Inf -> "null"   5e-324 -> "5e-324"

Positive cases assert the exact Node-oracle text (must prove), including a
5-deep nested array that defeats any fixed-bounded (stalling) serializer.
The single negative case (neg-escape) asserts an unescaped control char must
not be emitted raw (must reject with a Pure assertion failure on the Assert
line, not a cutoff or crash).
"""

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
    ("json-serialize-core", "wpst", None, True),
    ("json-serialize-nested", "wpst", None, True),
    ("json-serialize-empty", "wpst", None, True),
    ("json-serialize-escapes", "wpst", None, True),
    ("json-serialize-keyorder", "wpst", None, True),
    ("json-serialize-numbers", "wpst", None, True),
    ("json-serialize-neg-escape", "wpst", None, False),
    ("json-serialize-depth", "wpst", None, True),
]


def run_case(name, mode, proc, expected_success, output):
    source = ROOT / (name + ".js")
    case_dir = output / name
    case_dir.mkdir()
    command = COMMAND + [mode, str(source), "--logging=normal", "--json-ui", "--unroll=100"]
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
                                   timeout=300, check=False)
    except subprocess.TimeoutExpired:
        return result | {"passed": False, "reason": "timeout"}
    text = execution.stdout
    (case_dir / "output.log").write_text(text)
    log = case_dir / "file.log"
    incomplete = any(marker in (log.read_text(errors="replace") if log.exists() else "")
                     for marker in ("MAX BRANCHING", "Stopping Symbolic Execution"))
    result.update(exitCode=execution.returncode, incomplete=incomplete)
    try:
        payload = text.split("===JSON RESULTS===", 1)[1].lstrip()
        paths, _ = json.JSONDecoder().raw_decode(payload)
    except (IndexError, ValueError):
        return result | {"passed": False, "reason": "missing path results"}
    failures = [p for p in paths if p[0] == "RFail"]
    normal = [p for p in paths if p[0] == "RSucc" and p[1]["flag"] == ["Normal"]]
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
    return result | {"passed": passed and not incomplete}


if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-json-serialize-"))
    results = []
    for case in CASES:
        result = run_case(*case, output)
        results.append(result)
        print(f"{case[0]}: {'PASS' if result['passed'] else 'FAIL'}", flush=True)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"Evidence: {output}")
    raise SystemExit(0 if all(result["passed"] for result in results) else 1)
