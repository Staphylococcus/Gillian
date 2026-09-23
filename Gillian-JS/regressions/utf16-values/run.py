#!/usr/bin/env python3
"""Typed UTF-16 primitives: total proofs and required domain failures."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get('GILLIAN_JS', 'gillian-js'))
TOTAL = (0, 'All total procedure specs succeeded')
POST = (1, "Couldn't satisfy postcondition")
DOMAIN = (1, 'not proved defined')
CASES = [
    ('erased-rounded-length.gil', ['--total'], DOMAIN),
    ('erased-position.gil', ['--total'], DOMAIN),
    ('proof-partial-rounded-length.gil', ['--total'], DOMAIN),
    ('proof-partial-position.gil', ['--total'], DOMAIN),
    ('ordering-branch.gil', ['--total'], (125, 'binop: u16<')),
    ('format-type.gil', ['--total'], DOMAIN),
    ('parse-type.gil', ['--total'], DOMAIN),
    ('index.gil', ['--total'], TOTAL),
    ('index-oob.gil', ['--total'], DOMAIN),

    ('concat.gil', ['--total'], TOTAL),
    ('cancellation.gil', ['--total'], TOTAL),
    ('wrong-order.gil', ['--total'], POST),
    ('astral.gil', ['--total'], TOTAL),
    ('wrong-byte-length.gil', ['--total'], POST),
    ('wrong-code-point-length.gil', ['--total'], POST),
    ('raw-byte-input.gil', ['--total'], DOMAIN),
    ('byte-operation.gil', ['--total'], DOMAIN),
    ('untyped-input.gil', ['--total'], DOMAIN),
    ('mixed-concat.gil', ['--total'], DOMAIN),
    ('erased-domain.gil', ['--total'], DOMAIN),
    ('short-circuit.gil', ['--total'], TOTAL),
    ('proof-self-support.gil', ['--total'], DOMAIN),
    ('proof-guarded.gil', ['--total'], TOTAL),
    ('type-separation.gil', ['--total'], TOTAL),
]

if __name__ == '__main__':
    output = Path(tempfile.mkdtemp(prefix='gillian-utf16-values-',
                                  dir=os.environ.get('GILLIAN_RESULTS_ROOT')))
    results = []
    for index, (file, options, expected) in enumerate(CASES):
        source = ROOT / file
        directory = output / f'{index:02d}-{source.stem}'
        directory.mkdir()
        command = COMMAND + ['verify', str(source), '--logging=normal', '-a'] + options
        record = {'file': file, 'command': command, 'expectedExit': expected[0],
                  'expectedMessage': expected[1],
                  'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        try:
            run = subprocess.run(command, cwd=directory, capture_output=True,
                                 text=True, errors='replace', timeout=45)
            text = run.stdout + run.stderr
            (directory / 'output.log').write_text(text)
            passed = run.returncode == expected[0] and expected[1] in text
            if expected[0] != 0:
                passed &= TOTAL[1] not in text
            record |= {'passed': passed, 'exitCode': run.returncode, 'output': text}
        except subprocess.TimeoutExpired:
            record |= {'passed': False, 'reason': 'timeout'}
        results.append(record)
        print(f'{file}: {"PASS" if record["passed"] else "FAIL"}', flush=True)
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'Evidence: {output}')
    raise SystemExit(0 if all(r['passed'] for r in results) else 1)
