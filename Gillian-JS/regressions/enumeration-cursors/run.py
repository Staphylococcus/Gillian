#!/usr/bin/env python3
"""Exercise compiled enumeration; the wrong-result control must throw."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get('GILLIAN_JS', 'gillian-js'))
CASES = json.loads((ROOT / 'cases.json').read_text())

def program(case):
    expected = json.dumps(case['expected'], ensure_ascii=True)
    return ('"use strict";\nvar observed = (function() { ' + case['body'] + ' })();\n'
            + 'if (observed !== ' + expected + ') throw "enumeration result mismatch";\ntrue;\n')

if __name__ == '__main__':
    output = Path(tempfile.mkdtemp(prefix='enumeration-cursors-',
                                  dir=os.environ.get('GILLIAN_RESULTS_ROOT')))
    rows = []
    for case in CASES:
        directory = output / case['name']
        directory.mkdir()
        source = directory / 'case.js'
        source.write_text(program(case))
        command = COMMAND + ['exec', str(source), '--debug', '--logging=normal',
                             '--output', str(directory / 'compiled.gil')]
        start = time.monotonic()
        try:
            run = subprocess.run(command, cwd=directory, capture_output=True, timeout=45)
            raw = run.stdout + run.stderr
            (directory / 'output.bin').write_bytes(raw)
            primitive = dict(argv=command, returncode=run.returncode,
                             signal=-run.returncode if run.returncode < 0 else None,
                             seconds=time.monotonic() - start,
                             stdoutSha256=hashlib.sha256(raw).hexdigest())
            (directory / 'producer.json').write_text(json.dumps(primitive, indent=2) + '\n')
            text = raw.decode(errors='replace')
            reject = case.get('reject', False)
            expected_exit = int(reject)
            expected_marker = ('SUCCESSFUL TERMINATION: (error, u16"enumeration result mismatch")'
                               if reject else 'SUCCESSFUL TERMINATION: (normal, true)')
            row = dict(name=case['name'], **primitive,
                       sourceSha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                       passed=run.returncode == expected_exit and expected_marker in text)
        except subprocess.TimeoutExpired as exc:
            (directory / 'output.bin').write_bytes((exc.stdout or b'') + (exc.stderr or b''))
            row = dict(name=case['name'], passed=False, timedOut=True,
                       seconds=time.monotonic() - start)
            (directory / 'producer.json').write_text(json.dumps(row, indent=2) + '\n')
        (directory / 'report.json').write_text(json.dumps(row, indent=2) + '\n')
        rows.append(row)
        (output / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
        print(f"{case['name']}: {'PASS' if row['passed'] else 'FAIL'}", flush=True)
        if not row['passed']:
            break
    print(f'Evidence: {output}')
    raise SystemExit(0 if len(rows) == len(CASES) and all(r['passed'] for r in rows) else 1)
