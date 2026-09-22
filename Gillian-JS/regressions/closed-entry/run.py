#!/usr/bin/env python3
"""Closed empty-state entry proofs must never become procedure summaries."""
import hashlib, json, os, shlex, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
COMMAND = shlex.split(os.environ.get('GILLIAN_JS', 'gillian-js'))
SUCCESS = 'Closed entry postcondition succeeded'
BASE = ['--total', '--closed-entry', '--proc=main']
CASES = [
 ('fresh', BASE, 0, SUCCESS),
 ('cell', BASE, 0, SUCCESS),
 ('helper', BASE, 0, SUCCESS),
 ('assert', BASE, 0, SUCCESS),
 ('wrong', BASE, 1, "Couldn't satisfy postcondition"),
 ('cell-wrong', BASE, 1, "Couldn't satisfy postcondition"),
 ('helper-wrong', BASE, 1, "Couldn't satisfy postcondition"),
 ('assert-wrong', BASE, 1, 'Pure assertion failed'),
 ('collision', BASE, 124, 'requires fresh allocation'),
 ('generated-name', BASE, 124, 'cannot name a generated concrete location'),
 ('generated-post', BASE, 124, 'cannot name a generated concrete location'),
 ('generated-predicate', BASE, 124, 'cannot name a generated concrete location'),
 ('precondition', BASE, 124, 'requires no parameters and one normal emp specification'),
 ('parameters', BASE, 124, 'requires no parameters and one normal emp specification'),
 ('macro-fold', BASE, 124, 'closed entry cannot abstract or assume heap resources'),
 ('assume', BASE, 124, 'outside the totality fragment'),
 ('recursive', BASE, 124, 'needs a recursive-call variant'),
 ('loop', BASE, 124, 'control-flow cycle without a ranked invariant'),
 ('helper-summary', BASE, 124, 'must be selected and proved total'),
 ('fresh', ['--closed-entry', '--proc=main'], 124, 'requires --total'),
 ('two', ['--total', '--closed-entry'], 124, 'exactly one procedure'),
 ('fresh', ['--total', '--proc=main'], 124, 'requires fresh allocation'),
]
if __name__ == '__main__':
 output = Path(tempfile.mkdtemp(prefix='gillian-closed-entry-', dir=os.environ.get('GILLIAN_RESULTS_ROOT')))
 results = []
 for i, (name, args, code, message) in enumerate(CASES):
  source = ROOT / (name + '.gil'); directory = output / f'{i}-{name}'; directory.mkdir()
  command = COMMAND + ['verify', str(source), '-a', '--logging=normal'] + args
  record = {'file':source.name, 'args':args, 'expectedExit':code, 'expectedMessage':message,
            'sourceSha256':hashlib.sha256(source.read_bytes()).hexdigest()}
  try:
   r = subprocess.run(command, cwd=directory, capture_output=True, text=True, timeout=45)
   log = r.stdout + r.stderr; (directory/'output.log').write_text(log)
   record |= {'exitCode':r.returncode, 'output':log,
              'passed':r.returncode == code and message in log and 'All total procedure specs succeeded' not in log
                        and (code == 0 or SUCCESS not in log)
                        and not list(directory.rglob('verif_results.json'))}
  except subprocess.TimeoutExpired:
   record |= {'passed':False, 'reason':'timeout'}
  results.append(record); print(name, args, 'PASS' if record['passed'] else 'FAIL', flush=True)
 (output/'results.json').write_text(json.dumps(results, indent=2)+'\n')
 print('Evidence:', output)
 raise SystemExit(0 if all(r['passed'] for r in results) else 1)
