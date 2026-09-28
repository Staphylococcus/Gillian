#!/usr/bin/env python3
"""Check exact Boolean integer procedure ranks through the ordinary JS import route."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
CASES = [
    ("ranked", 0, "All total procedure specs succeeded"),
    ("wrong-post", 1, "Couldn't satisfy postcondition"),
    ("no-progress", 1, "variant is not a strictly smaller natural integer"),
    ("constant-rank", 1, "variant is not a strictly smaller natural integer"),
    ("missing-rank", 124, "step needs a recursive-call variant"),
    ("nonformal-rank", 124, "step variant must use only formal program parameters."),
]
HARD = re.compile(
    r"Internal error!|Segmentation fault|core dumped|\bAborted\b|Parser Error|"
    r"Syntax error|unexpected token|Cannot resolve|Failed to import|"
    r"timeout: sending signal|killed by timeout|Incomplete totality proof: SMT returned unknown",
    re.IGNORECASE,
)
POST = "VERIFICATION FAILURE in spec step (0, 0): Couldn't satisfy postcondition"
SUCCESS = re.compile(r"Verifying one spec of procedure step\.\.\..*?\bs Success\b")


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def put(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def scan(path):
    facts = {"hard": [], "namedPostFailure": False, "sha256": sha(path)}
    with path.open(errors="replace") as stream:
        for line_no, line in enumerate(stream, 1):
            if HARD.search(line):
                facts["hard"].append(line_no)
            if POST in line:
                facts["namedPostFailure"] = True
    return facts


def classify(name, returncode, timed_out, stdout, verbose):
    expected = next(row for row in CASES if row[0] == name)
    one_test = stdout.count("Obtained 1 symbolic tests in total") == 1
    success = len(SUCCESS.findall(stdout))
    all_total = stdout.count("All total procedure specs succeeded")
    passed = (type(returncode) is int and returncode == expected[1]
              and not timed_out and not HARD.search(stdout) and not verbose["hard"]
              and stdout.count(expected[2]) == 1)
    passed &= not any(x in stdout for x in ["Execution failure", "Failed to create matching plan", "Predicate "])
    if name == "ranked":
        passed &= one_test and success == 1 and all_total == 1 and stdout.count("Verifying one spec of procedure step...") == 1
        passed &= not verbose["namedPostFailure"] and "VERIFICATION FAILURE" not in stdout
    else:
        passed &= success == 0 and all_total == 0
        if name in ("missing-rank", "nonformal-rank"):
            passed &= "Obtained" not in stdout and "Verifying one spec" not in stdout
        else:
            passed &= not "Unsupported totality proof:" in stdout
            passed &= one_test and "Verifying one spec of procedure step..." in stdout
            if name == "wrong-post":
                passed &= verbose["namedPostFailure"] and "Failure" in stdout
    return {"controlPassed": bool(passed), "oneTest": one_test,
            "successes": success, "allTotalSuccess": all_total, "verbose": verbose}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="fresh evidence directory")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source_pins = {p.name: sha(p) for p in ROOT.iterdir() if p.is_file()}
    put(args.out / "sources.json", source_pins)
    command = shlex.split(os.environ.get("GILLIAN_JS", "gillian-js"))
    runtime = os.environ.get("GILLIAN_RUNTIME")
    records = []
    for name, _, _ in CASES:
        directory = args.out / name
        directory.mkdir()
        shutil.copyfile(ROOT / "entry.js", directory / "entry.js")
        shutil.copyfile(ROOT / (name + ".jsil"), directory / "Ranked.jsil")
        argv = command + ["verify", "entry.js", "--total", "--proc=step",
                          "--logging=verbose", "--dump-smt"]
        if runtime:
            argv += ["-R", runtime]
        start = time.monotonic()
        timed_out = False
        with (directory / "output.bin").open("wb") as output:
            proc = subprocess.Popen(argv, cwd=directory, stdout=output, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            try:
                proc.wait(timeout=45)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
        primitive = {"argv": argv, "returncode": proc.returncode,
                     "signal": -proc.returncode if proc.returncode < 0 else None,
                     "timedOut": timed_out, "seconds": time.monotonic() - start,
                     "stdoutSha256": sha(directory / "output.bin")}
        put(directory / "producer.json", primitive)  # Retain before interpreting any outcome.
        shutil.copyfile(directory / "output.bin", directory / "output.log")
        assert (directory / "output.bin").stat().st_size < 2**20, "oversized summary retained"
        text = (directory / "output.bin").read_text(errors="replace")
        verbose = scan(directory / "file.log")
        record = classify(name, proc.returncode, timed_out, text, verbose)
        unchanged = source_pins == {p.name: sha(p) for p in ROOT.iterdir() if p.is_file()}
        unchanged &= sha(directory / "entry.js") == source_pins["entry.js"]
        unchanged &= sha(directory / "Ranked.jsil") == source_pins[name + ".jsil"]
        record.update(case=name, producer=primitive, inputsUnchanged=unchanged,
                      proofAccepted=False, certificationReady=False, fullProofDone=False)
        record["controlPassed"] &= unchanged
        put(directory / "report.json", record)
        records.append(record)
        put(args.out / "results.json", records)
        print(f"{name}: {'PASS' if record['controlPassed'] else 'FAIL'}", flush=True)
        if not record["controlPassed"]:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
