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
    ("distinct-indices.gil", ["--total"], TOTAL),
    ("distinct-indices-wrong.gil", ["--total"], POST),
    ("distinct-indices-equal.gil", ["--total"], POST),
    ("formatter-set-keys.gil", ["--total"], TOTAL),
    ("formatter-set-keys-wrong.gil", ["--total"], POST),
    ("nan-key-equality.gil", ["--total"], TOTAL),
    ("nan-key-equality-wrong.gil", ["--total"], POST),
    ("ordered-number-keys.gil", ["--total"], TOTAL),
    ('constant-min-scientific.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('scientific-positive.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('scientific-negative-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),

    ('constant-pi.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('constant-pi-false-proof.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('constant-max-safe.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('constant-epsilon.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('constant-min-alias.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('constant-max-alias.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('constant-random.gil', ['--total'], (124, 'nondeterministic runtime constants need an explicit model')),
    ('constant-utc.gil', ['--total'], (124, 'nondeterministic runtime constants need an explicit model')),
    ('constant-local.gil', ['--total'], (124, 'nondeterministic runtime constants need an explicit model')),

    ('uint32-zero-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('noncanonical-false-proof.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('canonical-one.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('noncanonical-exclusion.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('zero.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('zero-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('infinity.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('negative-infinity.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('nan.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('congruence.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('congruence-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('key-collision.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('parse-space-zero.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-space-false-nan.js', ['--total', '--proc=answer'], (1, "Couldn't satisfy postcondition")),
    ('parse-unicode-zero.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-decimal-grammar.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-radix.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-invalid-separator.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-invalid-signed-radix.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('parse-nonspace.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('uint32-range.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('int32-range.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('uint16-range.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('uint32-negative.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('uint32-negative-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('uint32-zero.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('integer-length.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('format-parse.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('format-parse-non-nan.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('format-parse-zero.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('format-parse-zero-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('format-parse-nan.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('integer-fraction.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('integer-fraction-wrong.gil', ['--total'], (1, "Couldn't satisfy postcondition")),
    ('integer-nan.gil', ['--total'], (0, 'All total procedure specs succeeded')),
    ('actual-to-length.gil', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('actual-array-index.gil', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
    ('javascript-format-parse.js', ['--total', '--proc=answer'], (0, 'All total procedure specs succeeded')),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-number-text-soundness-",
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
