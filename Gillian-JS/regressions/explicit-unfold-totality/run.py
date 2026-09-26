#!/usr/bin/env python3
"""Run the explicit-unfold-totality controls once each against the frozen backend.

Usage: run.py <backend-root> <output-root> [--cases CASE [CASE ...]]

Each selected case runs exactly once via docker; stop on the first failed
control. Raw receipts are written before classification. No retries or repairs.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

INVENTORY_PATH = '/home/vas/dev/fold-cc-poc/experiments/full-proof/inventory.py'
IMAGE_ID = 'sha256:cf1c78e15d8184a8bacb65bc0e604b4395558999d218c93d6a84b965f3c37b51'
FROZEN_BACKEND_JSON = '/tmp/hermes-unfold-controls-p071/frozen-backend.json'
FROZEN_BACKEND_SHA = '28fc3c88af177cfed92861b5e0306b2510355eeff4924ad3c5007af8ea2b7ff6'
INVENTORY_SHA = '804169faa216cc40a2ded00941c05593e0aadd872ba02011c47852a32e750ae3'
MIN_FREE_BYTES = 128 * 1024 ** 3

CASES = ['positive', 'wrong-post', 'all-infeasible']

# The six named source files of this card, each frozen as its own explicit
# file group (no directory tree, so pycache or stray files cannot slip in).
SOURCE_FILES = ['run.py', 'test_runner.py', 'README.md',
                'positive.gil', 'wrong-post.gil', 'all-infeasible.gil']


def load_inventory():
    spec = importlib.util.spec_from_file_location('inventory', INVENTORY_PATH)
    if spec is None:
        sys.exit(f'cannot load inventory helper: {INVENTORY_PATH}')
    if file_sha(INVENTORY_PATH) != INVENTORY_SHA:
        sys.exit("inventory helper hash mismatch; refusing to load")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


DOCKER_SCRIPT = (
    'set -e\n'
    'cd /results\n'
    'cp /cases/case.gil .\n'
    'exec timeout --verbose -k 5 45 opam exec -- /work/_build/default/Gillian-JS/bin/gillian_js.exe '
    'verify case.gil -a --total --dump-smt --logging=verbose '
    '-R /work/_build/install/default/share/gillian-js/runtime '
    '--proc=answer --lemma=CheckChoice\n'
)


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description='Run the explicit-unfold-totality controls once each.')
    parser.add_argument('backend_root')
    parser.add_argument('output_root')
    parser.add_argument('--cases', nargs='+', choices=CASES, default=list(CASES),
                        metavar='CASE',
                        help='cases to run, in the given order (default: all)')
    args = parser.parse_args(argv)
    if len(set(args.cases)) != len(args.cases):
        # Rejected before any output is created.
        parser.error(f'duplicate --cases entries: {args.cases}')
    return args


def ensure_fresh_output_root(output_root):
    if output_root.exists() or output_root.is_symlink():
        sys.exit(f'output root must not exist (even empty): {output_root}')
    # No exist_ok: refuse reuse, never move completed output paths.
    output_root.mkdir(parents=True)


def source_groups(fixture_dir, backend_root, bin_path):
    groups = [{'role': f'source-{name}', 'path': str(fixture_dir / name), 'kind': 'file'}
              for name in SOURCE_FILES]
    groups += [
        {'role': 'backend-git-source', 'path': str(backend_root), 'kind': 'git'},
        {'role': 'backend-binary', 'path': str(bin_path), 'kind': 'file'},
        {'role': 'installed-runtime',
         'path': str(backend_root / '_build/install/default/share/gillian-js/runtime'),
         'kind': 'tree'},
        {'role': 'inventory-helper', 'path': INVENTORY_PATH, 'kind': 'file'},
        {'role': 'frozen-backend-json', 'path': FROZEN_BACKEND_JSON, 'kind': 'file'},
    ]
    return groups


def pin_mismatches(pin_map_path, expected_map_sha, pin_map=None, sha_fn=None):
    """Return [(path, actual, expected)] for every drifted frozen pin.

    Checks the pin map's own hash AND every file hash it contains, so a
    drifted non-binary pin is detected, not just the backend binary.
    """
    if sha_fn is None:
        sha_fn = file_sha
    actual_map_sha = sha_fn(pin_map_path)
    if actual_map_sha != expected_map_sha:
        # The map itself drifted: report that single mismatch immediately and
        # never parse or traverse a possibly-rewritten map.
        return [[str(pin_map_path), actual_map_sha, expected_map_sha]]
    if pin_map is None:
        pin_map = json.loads(Path(pin_map_path).read_text())
    problems = []
    for path, expected in sorted(pin_map.items()):
        try:
            actual = sha_fn(path)
        except OSError:
            # Missing/unreadable pinned file: report, keep checking others.
            problems.append([str(path), None, expected])
            continue
        if actual != expected:
            problems.append([str(path), actual, expected])
    return problems


def verify_staged_executed(staged, executed):
    """Both case files must be regular non-symlink files with equal bytes."""
    problems = []
    for label, path in (('staged', staged), ('executed', executed)):
        if path.is_symlink():
            problems.append(f'{label} case is a symlink: {path}')
        elif not path.is_file():
            problems.append(f'{label} case missing or not a regular file: {path}')
    if not problems and staged.read_bytes() != executed.read_bytes():
        problems.append('executed case.gil bytes differ from staged case.gil')
    return problems


def run_postchecks(inv, groups, before, staged_group, staged_snap, staged,
                   case_results_dir):
    """After EVERY producer: frozen groups, staged bytes, executed case, pins."""
    inv.assert_unchanged(groups, before)
    inv.assert_unchanged([staged_group], staged_snap)
    problems = verify_staged_executed(staged, case_results_dir / 'case.gil')
    problems += [f'frozen pin drift: {p[0]}' for p in pin_mismatches(
        FROZEN_BACKEND_JSON, FROZEN_BACKEND_SHA)]
    if problems:
        raise ValueError('; '.join(problems))


def build_command(image_id, backend_root, case_dir, case_results_dir):
    return [
        'docker', 'run', '--rm', '--network', 'none', '--cpus', '2', '--memory', '2g',
        '--entrypoint', 'bash',
        '-v', f'{backend_root}:/work:ro',
        '-v', f'{case_dir}:/cases:ro',
        '-v', f'{case_results_dir}:/results',
        image_id, '-c', DOCKER_SCRIPT,
    ]


def require_disk_free(output_root):
    free = shutil.disk_usage(output_root).free
    if free < MIN_FREE_BYTES:
        sys.exit(f'insufficient free disk for output root: {free} < {MIN_FREE_BYTES}')
    return free


def run_selected_cases(selected_cases, fixture_dir, image_id, backend_root,
                       output_root, inv, groups, before, reports, producer_receipts):
    """Run once per selected case; retain actual receipts and stop on failure."""
    halted = None
    first_free = last_free = None
    for name in selected_cases:
        if halted is not None:
            reports[name] = {'status': 'skipped', 'reason': halted}
            continue
        free_before = require_disk_free(output_root)
        if first_free is None:
            first_free = free_before
        case_dir = output_root / 'cases' / name
        case_dir.mkdir()
        staged = case_dir / 'case.gil'
        staged.write_bytes((fixture_dir / f'{name}.gil').read_bytes())
        staged_group = {'role': f'staged-{name}', 'path': str(staged), 'kind': 'file'}
        staged_snap = inv.snapshot([staged_group])
        write_json(case_dir / 'input-inventory.json',
                   {'groups': [staged_group], 'snapshot': staged_snap})
        result_dir = output_root / 'results' / name
        result_dir.mkdir(parents=True)
        cmd = build_command(image_id, backend_root, case_dir, result_dir)
        start = time.monotonic()
        proc = subprocess.run(cmd, capture_output=True)
        elapsed = round(time.monotonic() - start, 3)
        raw = proc.stdout + proc.stderr
        raw_sha = hashlib.sha256(raw).hexdigest()
        output_bin, output_log = result_dir / 'output.bin', result_dir / 'output.log'
        output_bin.write_bytes(raw)
        output_log.write_bytes(raw)
        verbose_log = result_dir / 'file.log'
        last_free = verbose_sha = None
        text_verbose = ''
        errors = []
        try:
            last_free = shutil.disk_usage(output_root).free
            if last_free < MIN_FREE_BYTES:
                raise ValueError(f'insufficient free disk after producer: {last_free}')
            if verbose_log.is_file():
                verbose_sha = inv.sha(verbose_log)
                text_verbose = verbose_log.read_text(errors='replace')
        except Exception as error:
            errors.append(f'metadata capture failed: {type(error).__name__}: {error}')
        # Metadata failures are caught; immutable process evidence always precedes
        # classification and all input postchecks.
        receipt = {
            'case': name, 'command': cmd, 'returncode': proc.returncode,
            'signal': abs(proc.returncode) if proc.returncode < 0 else None,
            'negativeSignal': proc.returncode if proc.returncode < 0 else None,
            'elapsedSeconds': elapsed, 'rawOutputSha256': raw_sha,
            'rawOutputBytes': len(raw), 'diskFreeBytesBefore': free_before,
            'diskFreeBytesAfter': last_free, 'stagedGroup': staged_group,
            'stagedInventory': staged_snap, 'outputBin': str(output_bin),
            'outputLog': str(output_log),
            'verboseLog': str(verbose_log) if verbose_sha else None,
            'verboseLogSha256': verbose_sha,
            'metadataError': '; '.join(errors) or None,
        }
        producer_receipts.append(receipt)
        write_json(result_dir / 'producer.json', receipt)
        classification = classify(name, proc.returncode,
                                  raw.decode('utf-8', errors='replace'), text_verbose)
        inputs_unchanged = False
        try:
            run_postchecks(inv, groups, before, staged_group, staged_snap,
                           staged, result_dir)
            inputs_unchanged = True
        except Exception as error:
            errors.append(f'postchecks failed: {type(error).__name__}: {error}')
        report = {
            **classification, 'rawOutputSha256': raw_sha,
            'controlPassed': classification['controlPassed'] and not errors,
            'inputsUnchanged': inputs_unchanged,
            'checksFailed': '; '.join(errors) or None,
            'proofAccepted': False, 'certificationReady': False, 'fullProofDone': False,
        }
        reports[name] = report
        write_json(result_dir / 'report.json', report)
        if errors:
            halted = f'{name}: ' + '; '.join(errors)
        elif not report['controlPassed']:
            halted = f'{name}: control did not pass rc={proc.returncode}'
    return halted, first_free, last_free


# Verdict classification. Pure: no I/O, no process state.
# `stdout` carries the named proof verdicts; `verbose` carries the proof
# diagnostics. Offsets refer to the stream actually searched.

# Named verdicts identify the EXACT selected name: dots are escaped and the
# phase tokens use a single-line wildcard, so 'CheckChoice.*?' can no longer
# match 'CheckChoiceOther...' and 'answer.*?' cannot match 'answerOther...'.
_STDOUT_OFFSETS = {
    'lemmaSuccess': r'Verifying lemma CheckChoice\.\.\..*? s Success',
    'specSuccess': r'Verifying one spec of procedure answer\.\.\..*? s Success',
    'allTotalSucceeded': r'All total procedure specs succeeded',
    'lemmaFailure': r'Verifying lemma CheckChoice\.\.\..*? f Failure',
    'noOutcomes': r'Incomplete total proof: lemma produced no outcomes',
    'unsupportedTotally': r'Unsupported totality proof: CheckChoice\b',
    'terminalSmtUnknown': r'Incomplete totality proof: SMT returned unknown',
}

_VERBOSE_OFFSETS = {
    'unfoldResult': r'Results of unfolding Choice\(n\)',
    'finalStateNonAdmissible': r'final state non admissible',
    # 'CheckChoice (' boundary so CheckChoiceOther is not accepted.
    'verificationFailureCheckChoice': r'VERIFICATION FAILURE in spec CheckChoice \(',
    'couldntSatisfyPostcondition': r"Couldn't satisfy postcondition",
    'solverUnknown': r'The solver returned: unknown',
}

# Hard-error diagnostics. Matching is case-insensitive (re.IGNORECASE in
# _any) because real diagnostics carry mixed or leading capitalization.
_CRASH_PATTERNS = [
    r'Segmentation fault',
    r'core dumped',
    r'Aborted',
    r'Internal error!',
]
_PARSER_PATTERNS = [
    r'parser error',
    r'syntax error',
    r'failed to parse',
    r'unexpected token',
]
_IMPORT_PATTERNS = [
    r'import error',
    r'failed to import',
    r'cannot import',
    r'Cannot resolve',
]
# Concrete outer-timeout kill messages only. The bare word "timeout" (which
# occurs in harmless log text) is deliberately NOT matched.
_TIMEOUT_KILL_PATTERNS = [
    r'killed by timeout',
    r'\btimeout:.*\bkilled\b',
    r'timeout: sending signal \w+',
    r'\bKILL\b',
]
# Shell termination by signal: 128+9 / 128+11 / 128+15. The process was
# killed before a verdict could be trusted, so these reject acceptance even
# when expected markers were printed earlier. 124 (timeout) stays allowed
# with correct evidence.
_SIGNAL_KILL_RCS = {137, 139, 143}


def _search(text, pattern):
    m = re.search(pattern, text)
    return m.start() if m else None


def _offsets(text, spec):
    return {key: _search(text, pat) for key, pat in spec.items()}


def _any(text, patterns):
    return any(re.search(p, text, re.IGNORECASE) for p in patterns)


def _same_line(text, a, b):
    idx = 0
    for line in text.splitlines(keepends=True):
        if a in line and b in line:
            return idx
        idx += len(line)
    return None


def _is_plain_int(value):
    return isinstance(value, int) and not isinstance(value, bool)


def classify(case, returncode, stdout, verbose):
    """Classify a control run's verdict from its captured streams.

    Pure function: no I/O or process state. Returns the classification dict
    (case / returncode / markers / expected / controlPassed /
    diagnosticOffsets). The caller adds rawOutputSha256 and sets halted when
    controlPassed is false.
    """
    out = {
        'case': case,
        'returncode': returncode,
        'markers': {},
        'expected': {},
        'controlPassed': False,
        'diagnosticOffsets': {
            'stdout': _offsets(stdout or '', _STDOUT_OFFSETS),
            'verbose': _offsets(verbose or '', _VERBOSE_OFFSETS),
        },
    }
    markers = out['markers']
    so = stdout or ''
    ve = verbose or ''
    # Hard diagnostics are checked in BOTH captured stdout and the verbose
    # stream: the producer merges stdout+stderr and the verbose log can
    # carry the same infrastructure diagnostics independently.
    hard_text = so + '\n' + ve
    markers['crashObserved'] = _any(hard_text, _CRASH_PATTERNS)
    markers['parserObserved'] = _any(hard_text, _PARSER_PATTERNS)
    markers['importObserved'] = _any(hard_text, _IMPORT_PATTERNS)
    markers['timeoutKillObserved'] = _any(hard_text, _TIMEOUT_KILL_PATTERNS)
    markers['terminalSmtUnknown'] = (
        _search(hard_text, r'Incomplete totality proof: SMT returned unknown') is not None)
    hard_fail = (markers['crashObserved'] or markers['parserObserved']
                 or markers['importObserved'] or markers['timeoutKillObserved']
                 or markers['terminalSmtUnknown'])
    named_lemma = _search(so, r'Verifying lemma CheckChoice\.\.\..*? s Success') is not None
    named_spec = _search(so, r'Verifying one spec of procedure answer\.\.\..*? s Success') is not None
    named_all = _search(so, r'All total procedure specs succeeded') is not None
    named_success = named_lemma or named_spec or named_all
    markers['namedLemmaSuccess'] = named_lemma
    markers['namedSpecSuccess'] = named_spec
    markers['namedAllTotalSuccess'] = named_all
    markers['namedSuccess'] = named_success
    signal_killed = _is_plain_int(returncode) and returncode in _SIGNAL_KILL_RCS
    markers['signalKilled'] = signal_killed

    if case not in CASES or not _is_plain_int(returncode) or returncode < 0:
        return out
    if case == 'positive':
        markers['unfoldTrace'] = (
            _search(ve, r'Results of unfolding Choice\(n\)') is not None)
        markers['finalStateNonAdmissible'] = (
            _search(ve, r'final state non admissible') is not None)
        markers['verificationFailure'] = (
            _search(ve, r'VERIFICATION FAILURE') is not None)
        out['controlPassed'] = bool(
            returncode == 0
            and named_lemma and named_spec and named_all
            and markers['unfoldTrace'] and markers['finalStateNonAdmissible']
            and not markers['verificationFailure']
            and not hard_fail
            and not signal_killed,
        )
    elif case == 'wrong-post':
        markers['lemmaFailure'] = (
            _search(so, r'Verifying lemma CheckChoice\.\.\..*? f Failure') is not None)
        sl_off = _same_line(
            ve, 'VERIFICATION FAILURE in spec CheckChoice (',
            "Couldn't satisfy postcondition")
        markers['sameLinePostFailure'] = sl_off is not None
        out['diagnosticOffsets']['verbose']['sameLinePostFailure'] = sl_off
        markers['unsupportedTotally'] = (
            _search(so, r'Unsupported totality proof: CheckChoice\b') is not None)
        out['controlPassed'] = bool(
            returncode > 0
            and markers['lemmaFailure'] and markers['sameLinePostFailure']
            and not named_success
            and not hard_fail
            and not signal_killed,
        )
    else:  # all-infeasible
        markers['noOutcomes'] = (
            _search(so, r'Incomplete total proof: lemma produced no outcomes') is not None)
        markers['finalStateNonAdmissible'] = (
            _search(ve, r'final state non admissible') is not None)
        out['controlPassed'] = bool(
            returncode > 0
            and markers['noOutcomes'] and markers['finalStateNonAdmissible']
            and not named_success
            and not hard_fail
            and not signal_killed,
        )
    return out


def finalize_run(output_root, inv, groups, before, reports,
                 producer_receipts, image_id, actual_bin_sha,
                 selected_cases, halted, disk_free_before, disk_free_after,
                 run_failed):
    """Retain final evidence on failure; never relabel child producer records."""
    reasons = [reason for reason in (halted, run_failed) if reason]
    pin_problems, after = [], None
    pin_reason = snapshot_reason = None
    try:
        pin_problems = pin_mismatches(FROZEN_BACKEND_JSON, FROZEN_BACKEND_SHA)
        if pin_problems:
            reasons.append(f'frozen pin drift: {pin_problems}')
    except Exception as error:
        pin_reason = f'final pin check failed: {type(error).__name__}: {error}'
        reasons.append(pin_reason)
    try:
        after = inv.snapshot(groups)
        if after != before:
            reasons.append('final snapshot differs from before')
    except Exception as error:
        snapshot_reason = f'final snapshot failed: {type(error).__name__}: {error}'
        reasons.append(snapshot_reason)
    inputs_unchanged = (after is not None and after == before and not pin_problems
                        and pin_reason is None and snapshot_reason is None)
    hashes = {}
    for key, path in [('frozenBackendJsonSha256', Path(FROZEN_BACKEND_JSON)),
                      ('inputInventorySha256', output_root / 'input-inventory.json')]:
        try:
            hashes[key] = inv.sha(path)
        except Exception as error:
            hashes[key] = None
            reasons.append(f'{key}: {type(error).__name__}: {error}')
    executed = [r['case'] for r in producer_receipts]
    controls_complete = (bool(selected_cases) and executed == list(selected_cases)
                         and all(reports.get(n, {}).get('controlPassed') is True
                                 and reports[n].get('inputsUnchanged') is True
                                 for n in selected_cases))
    if not controls_complete:
        reasons.append('not every selected control executed and passed with unchanged inputs')
    worker = {
        'card': os.environ.get('UNFOLD_CARD'),
        'topDriverExit': 3 if reasons else 0,
        'imageId': image_id, 'backendBinarySha256': actual_bin_sha, **hashes,
        'selectedCases': list(selected_cases), 'executedCases': executed,
        'inputsUnchangedAfter': inputs_unchanged, 'pinDriftProblems': pin_problems,
        'finalPinReason': pin_reason, 'finalSnapshotReason': snapshot_reason,
        'rehashedFrozenInputs': {i['path']: i['sha256'] for i in after['files']}
                               if after is not None else {},
        'producerReceipts': [{k: v for k, v in r.items()
                             if k not in ('stagedGroup', 'stagedInventory')}
                            for r in producer_receipts],
        'reports': dict(reports), 'halted': '; '.join(reasons) or None,
        'runFailed': run_failed, 'reasons': reasons,
        'diskFreeBytesBefore': disk_free_before, 'diskFreeBytesAfter': disk_free_after,
        'proofAccepted': False, 'certificationReady': False, 'fullProofDone': False,
        'evidenceComplete': True, 'evidenceError': None,
    }
    # Write the final report before taking ONE evidence snapshot, avoiding stale
    # self-receipts. On failure, explicitly retain an incomplete inventory instead.
    write_json(output_root / 'worker-result.json', worker)
    evidence_group = {'role': 'run-evidence', 'path': str(output_root),
                      'kind': 'tree', 'containerResults': True}
    evidence_error = None
    try:
        retained = inv.snapshot([evidence_group])
        inventory = {'complete': True, 'error': None, 'snapshot': retained}
    except Exception as error:
        evidence_error = f'run-evidence snapshot failed: {type(error).__name__}: {error}'
        reasons.append(evidence_error)
        worker.update(topDriverExit=3, evidenceComplete=False, evidenceError=evidence_error,
                      halted='; '.join(reasons))
        write_json(output_root / 'worker-result.json', worker)
        inventory = {'complete': False, 'error': evidence_error, 'snapshot': None}
    write_json(output_root / 'retained-files.json', inventory)
    return worker['topDriverExit'], worker['halted'], evidence_error, worker


def main(argv=None):
    args = parse_args(argv if argv is not None else sys.argv[1:])
    backend_root = Path(args.backend_root).resolve()
    output_root = Path(args.output_root).absolute()
    ensure_fresh_output_root(output_root)
    output_root = output_root.resolve()
    inv = load_inventory()
    if inv.sha(INVENTORY_PATH) != INVENTORY_SHA:
        sys.exit('inventory helper hash mismatch; refusing to run')
    if file_sha(FROZEN_BACKEND_JSON) != FROZEN_BACKEND_SHA:
        sys.exit('frozen-backend.json hash mismatch; refusing to run')
    pin_map = json.loads(Path(FROZEN_BACKEND_JSON).read_text())
    bin_path = backend_root / '_build/default/Gillian-JS/bin/gillian_js.exe'
    expected_bin_sha = pin_map.get(str(bin_path))
    actual_bin_sha = inv.sha(bin_path)
    if expected_bin_sha is None or actual_bin_sha != expected_bin_sha:
        sys.exit(f'backend binary sha mismatch: {actual_bin_sha} != {expected_bin_sha}')
    # All frozen pins must match before ANY subprocess is invoked.
    early_pins = pin_mismatches(FROZEN_BACKEND_JSON, FROZEN_BACKEND_SHA,
                                pin_map=pin_map)
    if early_pins:
        sys.exit('frozen pin mismatches; refusing to run:\n'
                 + '\n'.join(
                     f'  {path}: actual={actual} expected={expected}'
                     for path, actual, expected in early_pins))
    image_id = subprocess.run(
        ['docker', 'image', 'inspect', '--format', '{{.Id}}', IMAGE_ID],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    if image_id != IMAGE_ID:
        sys.exit(f'image ID mismatch: {image_id}')
    fixture_dir = Path(__file__).parent
    groups = source_groups(fixture_dir, backend_root, bin_path)
    before = inv.snapshot(groups)
    write_json(output_root / 'input-inventory.json',
               {'groups': groups, 'snapshot': before})
    (output_root / 'cases').mkdir()
    (output_root / 'results').mkdir()
    producer_receipts = []
    reports = {}
    halted = None
    disk_free_before = None
    disk_free_after = None
    run_failed = None
    try:
        halted, disk_free_before, disk_free_after = run_selected_cases(
            args.cases, fixture_dir, image_id, backend_root, output_root, inv,
            groups, before, reports, producer_receipts)
    except SystemExit as e:
        # A later disk-floor (or other) sys.exit is a HANDLED stop: raw
        # receipts written so far are preserved and evidence is still
        # finalized below.
        run_failed = f'SystemExit: {e.code}'
    except Exception as e:
        run_failed = f'{type(e).__name__}: {e}'
    if producer_receipts:
        disk_free_before = producer_receipts[0].get('diskFreeBytesBefore')
        disk_free_after = producer_receipts[-1].get('diskFreeBytesAfter')
    exit_code, halted, evidence_error, worker = finalize_run(
        output_root, inv, groups, before, reports, producer_receipts,
        image_id, actual_bin_sha, args.cases, halted, disk_free_before,
        disk_free_after, run_failed)
    print(json.dumps({
        'halted': halted,
        'reports': reports,
        'inputsUnchangedAfter': worker['inputsUnchangedAfter'],
        'evidenceComplete': evidence_error is None,
        'topDriverExit': exit_code,
    }, indent=2))
    sys.exit(exit_code)


if __name__ == '__main__':
    main()
