#!/usr/bin/env python3
"""Actual JS UTF-16 mapping: arbitrary inputs through compiled runtime bodies."""
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
ASSERT = (1, 'Assertion failed')
ORDERING = (125, 'binop: u16<')
# These whole-loop fixtures retain the original helper probe's 90-second cap.
# Existing per-procedure allowances and native SMT budgets stay unchanged.
WHOLE_LOOP_CASES = {'ucs2length.js', 'ucs2length-stalled.js',
                    'ucs2length-wrong-result.js', 'ucs2length-missing-context.js'}
CASES = [
    ('ucs2length.js', ['--total', '--proc=ucs2length'], TOTAL),
    ('ucs2length-stalled.js', ['--total', '--proc=ucs2length'],
     (1, 'variant is not a strictly smaller natural integer')),
    ('ucs2length-wrong-result.js', ['--total', '--proc=ucs2length'], POST),
    ('ucs2length-missing-context.js', ['--total', '--proc=ucs2length'],
     (1, 'MIFMetadata($lstr_proto)')),
    ('rank-one.js', ['--total', '--proc=check'], TOTAL),
    ('rank-two.js', ['--total', '--proc=check'], TOTAL),
    ('rank-two-wrong.js', ['--total', '--proc=check'], POST),
    ('rank-stalled.js', ['--total', '--proc=check'], POST),
    ('rank-missing-bound.js', ['--total', '--proc=check'], POST),
    ('rank-missing-integrality.js', ['--total', '--proc=check'], POST),
    ('surrogate-branch.js', ['--total', '--proc=check'], TOTAL),
    ('surrogate-branch-no-low.js', ['--total', '--proc=check'], POST),
    ('surrogate-branch-no-other.js', ['--total', '--proc=check'], POST),
    ('bitand-code-unit.js', ['--total', '--proc=check'], TOTAL),
    ('bitand-code-unit-wrong.js', ['--total', '--proc=check'], POST),
    ('charcodeat-mask.js', ['--total', '--proc=check'], TOTAL),
    ('charcodeat-mask-no-low.js', ['--total', '--proc=check'], POST),
    ('bitand.js', ['--total', '--proc=check'], TOTAL),
    ('bitand-wrong.js', ['--total', '--proc=check'], POST),
    ('bitand-mask.js', ['--total', '--proc=check'], TOTAL),
    ('bitand-mask-no-low.js', ['--total', '--proc=check'], POST),
    ('bitand-mask-no-other.js', ['--total', '--proc=check'], POST),
    ('second-unit-feasibility.js', ['--total', '--proc=check'], TOTAL),
    ('second-unit-no-inside.js', ['--total', '--proc=check'], POST),
    ('second-unit-no-outside.js', ['--total', '--proc=check'], POST),
    ('length-branch-feasibility.js', ['--total', '--proc=check'], TOTAL),
    ('length-branch-no-inside.js', ['--total', '--proc=check'], POST),
    ('length-branch-no-outside.js', ['--total', '--proc=check'], POST),
    ('length-language-bound.js', ['--total', '--proc=check'], TOTAL),
    ('length-language-bound-wrong.js', ['--total', '--proc=check'], POST),
    ('length-invariant-entry.js', ['--total', '--proc=check'], TOTAL),
    ('length-invariant-entry-wrong.js', ['--total', '--proc=check'], POST),
    ('length-nonnegative.js', ['--total', '--proc=check'], TOTAL),
    ('length-nonnegative-wrong.js', ['--total', '--proc=check'], POST),
    ('length-integral.js', ['--total', '--proc=check'], TOTAL),
    ('length-integral-wrong.js', ['--total', '--proc=check'], POST),
    ('charcodeat.js', ['--total', '--proc=check'], TOTAL),
    ('charcodeat-wrong-unit.js', ['--total', '--proc=check'], POST),
    ('charcodeat-wrong-nan.js', ['--total', '--proc=check'], POST),
    ('charcodeat-wrong-surrogate.js', ['--total', '--proc=check'], POST),
    ('charcodeat-initialize.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('charcodeat-initialized-units.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('charcodeat-initialized-empty.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('composition.js', ['--total', '--proc=check'], TOTAL),
    ('composition-negative-wrong.js', ['--total', '--proc=check'], POST),
    ('composition-outside-wrong.js', ['--total', '--proc=check'], POST),
    ('composition-inside-wrong.js', ['--total', '--proc=check'], POST),
    ('comparison-numbers-less.js', ['--total', '--proc=check'], TOTAL),
    ('comparison-numbers-less-wrong.js', ['--total', '--proc=check'], POST),
    ('comparison-numbers-leq.js', ['--total', '--proc=check'], TOTAL),
    ('comparison-numbers-leq-wrong.js', ['--total', '--proc=check'], POST),
    ('charat-direct-twice.js', ['--total', '--proc=check'], TOTAL),
    ('charat-direct-twice-wrong.js', ['--total', '--proc=check'], POST),
    ('charat-direct-independent.js', ['--total', '--proc=check'], TOTAL),
    ('charat-direct-independent-wrong.js', ['--total', '--proc=check'], POST),
    ('charat-twice.js', ['--total', '--proc=check', '--proc=twice', '--proof-dependency=twice:check'], TOTAL),
    ('charat-twice-wrong.js', ['--total', '--proc=check', '--proc=twice', '--proof-dependency=twice:check'], POST),
    ('charat-independent.js', ['--total', '--proc=check', '--proc=twice', '--proof-dependency=twice:check'], TOTAL),
    ('charat-independent-wrong.js', ['--total', '--proc=check', '--proc=twice', '--proof-dependency=twice:check'], POST),
    ('charat-independent.js', ['--total', '--proc=twice'], (124, 'check has not passed every totality proof case in this run')),
    ('charat-twice.js', ['--total', '--proc=twice'], (124, 'check has not passed every totality proof case in this run')),
    ('charat-initialize.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('charat-initialized-empty.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('charat-initialized-units.js', ['--total', '--closed-entry', '--proc=main'], (0, 'Closed entry postcondition succeeded')),
    ('charat-initialized-wrong-result.js', ['--total', '--closed-entry', '--proc=main'], POST),
    ('charat-initialized-wrong-method.js', ['--total', '--closed-entry', '--proc=main'], POST),
    ('charat-initialized-wrong-metadata.js', ['--total', '--closed-entry', '--proc=main'], POST),
    ('charat.js', ['--total', '--proc=check'], TOTAL),
    ('charat-unit-wrong.js', ['--total', '--proc=check'], POST),
    ('charat-empty-wrong.js', ['--total', '--proc=check'], POST),
    ('length-branches.js', ['--total', '--proc=check'], TOTAL),
    ('length-outside-wrong.js', ['--total', '--proc=check'], POST),
    ('length-inside-wrong.js', ['--total', '--proc=check'], POST),
    ('length.js', ['--total', '--proc=check'], TOTAL),
    ('length-wrong.js', ['--total', '--proc=check'], POST),
    ('length-zero-wrong.js', ['--total', '--proc=check'], POST),
    ('length-concrete.js', ['--total', '--proc=check'], TOTAL),
    ('length-codepoint-wrong.js', ['--total', '--proc=check'], POST),
    ('length-byte-wrong.js', ['--total', '--proc=check'], POST),
    ('ordering-branch.js', ['--total', '--proc=check'], ORDERING),
    ('ordering-concrete-wrong.js', ['--total', '--proc=check'], POST),
    ('fold-witness.js', ['--total', '--proc=check'], TOTAL),
    ('fold-witness-wrong.js', ['--total', '--proc=check'], ASSERT),
    ('concat.js', ['--total', '--proc=check'], TOTAL),
    ('cancellation.js', ['--total', '--proc=check'], TOTAL),
    ('typeof.js', ['--total', '--proc=check'], TOTAL),
    ('wrong-order.js', ['--total', '--proc=check'], POST),
    ('property.js', ['--total', '--proc=check'], TOTAL),
    ('numeric-key.js', ['--total', '--proc=check'], TOTAL),
]

if __name__ == '__main__':
    output = Path(tempfile.mkdtemp(prefix='gillian-js-utf16-values-',
                                  dir=os.environ.get('GILLIAN_RESULTS_ROOT')))
    results = []
    for index, (file, options, expected) in enumerate(CASES):
        source = ROOT / file
        directory = output / f'{index:02d}-{source.stem}'
        directory.mkdir()
        command = COMMAND + ['verify', str(source), '--logging=normal'] + options
        # Keep the existing per-procedure allowance when a case also checks
        # its callee before summary reuse. SMT query limits are unchanged.
        timeout_seconds = 90 if file in WHOLE_LOOP_CASES else 45 * max(1, sum(o.startswith('--proc=') for o in options))
        record = {'file': file, 'timeoutSeconds': timeout_seconds, 'command': command, 'expectedExit': expected[0],
                  'expectedMessage': expected[1],
                  'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        try:
            run = subprocess.run(command, cwd=directory, capture_output=True,
                                 text=True, errors='replace', timeout=timeout_seconds)
            text = run.stdout + run.stderr
            (directory / 'output.log').write_text(text)
            passed = run.returncode == expected[0] and expected[1] in text
            if expected[0] != 0:
                passed &= TOTAL[1] not in text
            record |= {'passed': passed, 'exitCode': run.returncode, 'output': text}
        except subprocess.TimeoutExpired as error:
            # Preserve partial diagnostics from rejected runs too.
            output_text = ''.join(part.decode(errors='replace') if isinstance(part, bytes)
                                  else part or '' for part in [error.stdout, error.stderr])
            (directory / 'output.log').write_text(output_text)
            record |= {'passed': False, 'reason': 'timeout'}
        results.append(record)
        print(f'{file}: {"PASS" if record["passed"] else "FAIL"}', flush=True)
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'Evidence: {output}')
    raise SystemExit(0 if all(r['passed'] for r in results) else 1)
