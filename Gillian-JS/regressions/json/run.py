#!/usr/bin/env python3
"""Execute the JS JSON model and controls, retaining all paths and cutoff logs."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
MODEL = REPO / 'Gillian-JS/runtime/JSON/json3.js'
COMMAND = shlex.split(os.environ.get('GILLIAN_JS', 'gillian-js'))
CASES = [(name, 'normal', 500) for name in ('roundtrip', 'unicode', 'special-keys', 'exceptions', 'hooks', 'numbers', 'symbolic-choice')] + [
    ('wrong-copy', 'assertion', 500), ('symbolic-string', 'unsupported', 500), ('roundtrip', 'cutoff', 0)]


def main():
    output = Path(tempfile.mkdtemp(prefix='gillian-json-', dir=os.environ.get('GILLIAN_RESULTS_ROOT')))
    runtime = output / 'runtime'
    shutil.copytree(REPO / '_build/install/default/share/gillian-js/runtime', runtime, symlinks=False)
    (runtime / 'InitFantine.jsil').chmod(0o644)
    shutil.copyfile(runtime / 'Init.jsil', runtime / 'InitFantine.jsil')
    results = []
    for name, expected, budget in CASES:
        directory = output / (name + '-' + expected)
        directory.mkdir()
        source = MODEL.read_text() + '\n' + (ROOT / (name + '.js')).read_text()
        target = directory / 'case.js'
        target.write_text(source)
        command = COMMAND + ['wpst', str(target), '-R', str(runtime), '--logging=normal', '--no-heap', '--json-ui', f'--unroll={budget}']
        record = dict(case=name, expected=expected, command=command, sourceSha256=hashlib.sha256(source.encode()).hexdigest())
        try:
            process = subprocess.run(command, cwd=directory, capture_output=True, text=True, errors='replace', timeout=120)
            text = process.stdout + process.stderr
            (directory / 'output.log').write_text(text)
            log = directory / 'file.log'
            cutoff = any(marker in (log.read_text(errors='replace') if log.exists() else '') for marker in ('MAX BRANCHING', 'Stopping Symbolic Execution'))
            paths = None
            if '===JSON RESULTS===' in process.stdout:
                paths, _ = json.JSONDecoder().raw_decode(process.stdout.split('===JSON RESULTS===', 1)[1].lstrip())
            normal = [p for p in paths or [] if p[0] == 'RSucc' and p[1]['flag'] == ['Normal']]
            if expected == 'normal':
                passed = process.returncode == 0 and bool(paths) and len(normal) == len(paths)
                if name == 'symbolic-choice': passed = passed and len(paths) == 2
            elif expected == 'assertion':
                passed = process.returncode == 1 and bool(paths) and all(p[0] == 'RFail' and p[1]['proc'] == 'main' and p[1]['errors'] == [['EState', ['EPure', ['Lit', ['Bool', False]]]]] for p in paths)
            elif expected == 'unsupported':
                passed = process.returncode != 0 and not normal and 'requires concrete operands' in text
            else:
                passed = cutoff
            record.update(passed=passed and (expected == 'cutoff' or not cutoff), exitCode=process.returncode, cutoff=cutoff, paths=paths)
        except subprocess.TimeoutExpired:
            record.update(passed=False, reason='timeout')
        results.append(record)
        print(f"{name} ({expected}): {'PASS' if record['passed'] else 'FAIL'}", flush=True)
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'Evidence: {output}')
    return 0 if all(r['passed'] for r in results) else 1

if __name__ == '__main__':
    raise SystemExit(main())
