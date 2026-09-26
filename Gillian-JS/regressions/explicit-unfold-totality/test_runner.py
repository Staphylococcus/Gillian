#!/usr/bin/env python3
"""Offline tests for the run.py verdict classifier.

Imports the local run.py module without executing main(), then exercises
classify() against synthetic streams. These are classifier tests only, not
symbolic proof. No Docker, no build, no verifier, no proof execution.

Run:
    /nix/store/m1fw8l8y9ycxh5dzispbb7cwl6rra14l-python3-3.13.12/bin/python3 -B \
        test_runner.py
"""
import importlib.util
import json
import os
import types
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUN_PY = HERE / 'run.py'


def _load_run():
    spec = importlib.util.spec_from_file_location('eu_run', RUN_PY)
    if spec is None:  # pragma: no cover - only on path failure
        raise RuntimeError(f'cannot load {RUN_PY}')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


RUN = _load_run()
classify = RUN.classify


# ---------------------------------------------------------------------------
# Synthetic stream builders.
# ---------------------------------------------------------------------------

POS_STDOUT = (
    'Verifying lemma CheckChoice... s Success\n'
    'Verifying one spec of procedure answer... s Success\n'
    'All total procedure specs succeeded\n'
)
POS_VERBOSE = (
    'Results of unfolding Choice(n):\n'
    '  final state non admissible\n'
)

WP_STDOUT = (
    'Verifying lemma CheckChoice... f Failure\n'
)
WP_VERBOSE = (
    "VERIFICATION FAILURE in spec CheckChoice (0, 0): "
    "Couldn't satisfy postcondition\n"
)
# A later, allowed downstream rejection line (genuine failed obligation).
WP_TAIL = 'Unsupported totality proof: CheckChoice has not passed every lemma proof case in this run.\n'

AI_STDOUT = 'Incomplete total proof: lemma produced no outcomes\n'
AI_VERBOSE = 'final state non admissible\n'

# Concrete failure phrases that must NOT be treated as generic.
TERMINAL_SMT_UNKNOWN = 'Incomplete totality proof: SMT returned unknown\n'
INTERIOR_SOLVER_UNKNOWN = 'The solver returned: unknown\n'
CRASH = 'Segmentation fault (core dumped)\n'
PARSER_ERR = 'parser error at line 1\n'
IMPORT_ERR = "cannot import module\n"
TIMEOUT_KILL = 'killed by timeout\n'  # generic word only; not a targeted phrase

# The four literal infrastructure diagnostics from the independent review,
# plus their mixed-case and KILL variants (hard matching is
# case-insensitive and must catch them in either stream).
GNU_TIMEOUT_TERM = 'timeout: sending signal TERM to command "opam"\n'
GNU_TIMEOUT_KILL = 'timeout: sending signal KILL to command "opam"\n'
SOLVER_BROKEN_PIPE = 'Internal error! Error when calling SMT solver: Broken pipe\n'
SYNTAX_UNEXPECTED_TOKEN = 'Syntax error: unexpected token\n'
CANNOT_RESOLVE_IMPORT = 'Cannot resolve imported file\n'


def _positive(verbose=POS_VERBOSE, stdout=POS_STDOUT, rc=0):
    return classify('positive', rc, stdout, verbose)


def _wrongpost(verbose=WP_VERBOSE, stdout=WP_STDOUT, rc=1):
    return classify('wrong-post', rc, stdout, verbose)


def _allinfeasible(verbose=AI_VERBOSE, stdout=AI_STDOUT, rc=1):
    return classify('all-infeasible', rc, stdout, verbose)


class PositiveTests(unittest.TestCase):
    def test_positive_expected(self):
        r = _positive()
        self.assertTrue(r['controlPassed'])
        # offsets refer to the stream actually searched
        self.assertIsNotNone(r['diagnosticOffsets']['verbose']['unfoldResult'])
        self.assertIsNotNone(r['diagnosticOffsets']['stdout']['lemmaSuccess'])
        self.assertIsNotNone(r['diagnosticOffsets']['verbose']['finalStateNonAdmissible'])

    def test_positive_missing_unfold_verbose_fails(self):
        r = classify('positive', 0, POS_STDOUT, 'final state non admissible\n')
        self.assertFalse(r['controlPassed'])

    def test_positive_missing_finalstate_verbose_fails(self):
        r = classify('positive', 0, POS_STDOUT, 'Results of unfolding Choice(n):\n')
        self.assertFalse(r['controlPassed'])

    def test_positive_verification_failure_fails(self):
        verbose = POS_VERBOSE + 'VERIFICATION FAILURE in spec X\n'
        self.assertFalse(classify('positive', 0, POS_STDOUT, verbose)['controlPassed'])

    def test_positive_nonzero_rc_fails(self):
        self.assertFalse(_positive(rc=1)['controlPassed'])

    def test_positive_interior_solver_unknown_still_passes(self):
        verbose = INTERIOR_SOLVER_UNKNOWN + POS_VERBOSE
        r = classify('positive', 0, POS_STDOUT, verbose)
        self.assertTrue(r['controlPassed'])


class WrongPostTests(unittest.TestCase):
    def test_wrongpost_expected(self):
        r = _wrongpost()
        self.assertTrue(r['controlPassed'])
        self.assertIsNotNone(r['diagnosticOffsets']['verbose']['sameLinePostFailure'])

    def test_wrongpost_same_line_required(self):
        verbose = ("VERIFICATION FAILURE in spec CheckChoice (0, 0): unrelated\n"
                   "Couldn't satisfy postcondition\n")
        r = classify('wrong-post', 1, WP_STDOUT, verbose)
        self.assertFalse(r['controlPassed'])
        self.assertIsNone(r['diagnosticOffsets']['verbose']['sameLinePostFailure'])

    def test_wrongpost_unrelated_failure_not_enough(self):
        stdout = 'Verifying lemma Other... f Failure\n'
        verbose = WP_VERBOSE
        r = classify('wrong-post', 1, stdout, verbose)
        self.assertFalse(r['controlPassed'])

    def test_wrongpost_named_success_contradiction(self):
        stdout = WP_STDOUT + POS_STDOUT
        r = classify('wrong-post', 1, stdout, WP_VERBOSE)
        self.assertFalse(r['controlPassed'])

    def test_wrongpost_exit124_valid_when_diagnostic_present(self):
        r = classify('wrong-post', 124, WP_STDOUT + WP_TAIL, WP_VERBOSE)
        self.assertTrue(r['controlPassed'])

    def test_wrongpost_interior_solver_unknown_still_passes(self):
        verbose = INTERIOR_SOLVER_UNKNOWN + WP_VERBOSE
        self.assertTrue(classify('wrong-post', 1, WP_STDOUT, verbose)['controlPassed'])


class AllInfeasibleTests(unittest.TestCase):
    def test_allinfeasible_expected(self):
        r = _allinfeasible()
        self.assertTrue(r['controlPassed'])

    def test_allinfeasible_verbose_success_false_does_not_invalidate(self):
        verbose = 'Success:false\n' + AI_VERBOSE
        r = classify('all-infeasible', 1, AI_STDOUT, verbose)
        self.assertTrue(r['controlPassed'])

    def test_allinfeasible_named_success_contradiction(self):
        stdout = AI_STDOUT + POS_STDOUT
        r = classify('all-infeasible', 1, stdout, AI_VERBOSE)
        self.assertFalse(r['controlPassed'])

    def test_allinfeasible_missing_finalstate_fails(self):
        r = classify('all-infeasible', 1, AI_STDOUT, '')
        self.assertFalse(r['controlPassed'])

    def test_allinfeasible_interior_solver_unknown_still_passes(self):
        verbose = INTERIOR_SOLVER_UNKNOWN + AI_VERBOSE
        self.assertTrue(classify('all-infeasible', 1, AI_STDOUT, verbose)['controlPassed'])


class ReturncodeAndCaseTests(unittest.TestCase):
    def _expect_false(self, **kw):
        defaults = dict(case='positive', returncode=0,
                        stdout=POS_STDOUT, verbose=POS_VERBOSE)
        defaults.update(kw)
        self.assertFalse(classify(**defaults)['controlPassed'])

    def test_bool_rc_rejected(self):
        self._expect_false(returncode=True)

    def test_null_rc_rejected(self):
        self._expect_false(returncode=None)

    def test_string_rc_rejected(self):
        self._expect_false(returncode='0')

    def test_negative_rc_rejected(self):
        self._expect_false(returncode=-1)

    def test_unknown_case_rejected(self):
        self._expect_false(case='bogus')

    def test_negative_rc_in_negatives_rejected(self):
        for case in ('wrong-post', 'all-infeasible'):
            defaults = dict(case=case, returncode=-1, stdout=POS_STDOUT, verbose=POS_VERBOSE)
            self.assertFalse(classify(**defaults)['controlPassed'])


class HardFailureTests(unittest.TestCase):
    # Each negative starts from its OWN passing fixture pair; the baseline is
    # asserted to pass before appending the disallowed diagnostic, so the
    # hard-failure guard itself is what flips the result.
    _BASELINES = {
        'wrong-post': (WP_STDOUT, WP_VERBOSE),
        'all-infeasible': (AI_STDOUT, AI_VERBOSE),
    }

    def _rejects(self, case, diag, stream, rc=124):
        base_out, base_ve = self._BASELINES[case]
        self.assertTrue(classify(case, 1, base_out, base_ve)['controlPassed'],
                        f'{case} baseline fixture pair must pass first')
        out, ve = (base_out + diag, base_ve) if stream == 'stdout' \
            else (base_out, base_ve + diag)
        r = classify(case, rc, out, ve)
        self.assertFalse(r['controlPassed'],
                         f'{case} rc={rc} must reject {diag!r} in {stream}')

    def _rejects_both_streams(self, diag, rc=124):
        for case in self._BASELINES:
            self._rejects(case, diag, 'stdout', rc)
            self._rejects(case, diag, 'verbose', rc)

    # The four literal infrastructure diagnostics from the independent
    # review (plus the KILL variant of the timeout message), in each stream
    # separately, with rc124.
    def test_gnu_timeout_term_rejected(self):
        self._rejects_both_streams(GNU_TIMEOUT_TERM)

    def test_gnu_timeout_kill_rejected(self):
        self._rejects_both_streams(GNU_TIMEOUT_KILL)

    def test_internal_error_broken_pipe_rejected(self):
        self._rejects_both_streams(SOLVER_BROKEN_PIPE)

    def test_syntax_unexpected_token_rejected(self):
        self._rejects_both_streams(SYNTAX_UNEXPECTED_TOKEN)

    def test_cannot_resolve_import_rejected(self):
        self._rejects_both_streams(CANNOT_RESOLVE_IMPORT)

    # Existing hard phrases keep failing, per-case and per-stream, rc124.
    def test_timeout_kill_rejected(self):
        self._rejects_both_streams(TIMEOUT_KILL)

    def test_bare_timeout_word_still_valid(self):
        # The generic word "timeout" alone must not invalidate; only
        # concrete kill diagnostics ("killed by timeout",
        # "timeout: sending signal ...", KILL) are hard failures.
        self.assertTrue(classify(
            'wrong-post', 124, WP_STDOUT + 'outer timeout budget\n', WP_VERBOSE,
        )['controlPassed'])
        self.assertTrue(classify(
            'all-infeasible', 124, AI_STDOUT + 'outer timeout budget\n', AI_VERBOSE,
        )['controlPassed'])

    def test_terminal_smt_unknown_rejected(self):
        self._rejects_both_streams(TERMINAL_SMT_UNKNOWN)

    def test_parser_error_rejected(self):
        self._rejects_both_streams(PARSER_ERR)

    def test_import_error_rejected(self):
        self._rejects_both_streams(IMPORT_ERR)

    def test_crash_rejected(self):
        self._rejects_both_streams(CRASH)

    def test_signal_kill_rcs_rejected(self):
        # 137/139/143 (128+SIGKILL/SIGSEGV/SIGTERM) reject even an
        # otherwise-valid negative; 124 remains allowed above.
        for rc in (137, 139, 143):
            for case in self._BASELINES:
                base_out, base_ve = self._BASELINES[case]
                self.assertTrue(classify(case, 1, base_out, base_ve)['controlPassed'])
                r = classify(case, rc, base_out, base_ve)
                self.assertFalse(r['controlPassed'], f'{case} rc={rc} must reject')

    def test_no_exception_raised(self):
        # Unknown case / weird rc must return a dict, never raise.
        for rc in (True, None, 'x', -3):
            r = classify('bogus', rc, 'junk', 'junk')
            self.assertIsInstance(r, dict)
            self.assertFalse(r['controlPassed'])


class ExactNameVerdictTests(unittest.TestCase):
    def test_positive_lemma_other_name_rejected(self):
        stdout = ('Verifying lemma CheckChoiceOther... s Success\n'
                  'Verifying one spec of procedure answer... s Success\n'
                  'All total procedure specs succeeded\n')
        self.assertFalse(classify('positive', 0, stdout, POS_VERBOSE)['controlPassed'])

    def test_positive_spec_other_name_rejected(self):
        stdout = ('Verifying lemma CheckChoice... s Success\n'
                  'Verifying one spec of procedure answerOther... s Success\n'
                  'All total procedure specs succeeded\n')
        self.assertFalse(classify('positive', 0, stdout, POS_VERBOSE)['controlPassed'])

    def test_wrongpost_checkchoiceother_failure_rejected(self):
        stdout = 'Verifying lemma CheckChoiceOther... f Failure\n'
        verbose = ("VERIFICATION FAILURE in spec CheckChoiceOther (0, 0): "
                   "Couldn't satisfy postcondition\n")
        r = classify('wrong-post', 1, stdout, verbose)
        self.assertFalse(r['controlPassed'])
        self.assertIsNone(r['diagnosticOffsets']['verbose']['sameLinePostFailure'])


class StructureTests(unittest.TestCase):
    def test_shape_and_expected_empty(self):
        r = _positive()
        for key in ('case', 'returncode', 'markers', 'expected',
                    'controlPassed', 'diagnosticOffsets'):
            self.assertIn(key, r)
        self.assertEqual(r['expected'], {})
        self.assertEqual(r['case'], 'positive')
        self.assertEqual(r['returncode'], 0)
        self.assertIn('stdout', r['diagnosticOffsets'])
        self.assertIn('verbose', r['diagnosticOffsets'])


# ---------------------------------------------------------------------------
# Selection / input-check tests for the new runner helpers (offline only:
# no Docker invocation, tiny temporary files, stdlib unittest/mock).
# ---------------------------------------------------------------------------

import tempfile
import unittest.mock as mock


class ParseArgsTests(unittest.TestCase):
    def test_default_is_all_cases_in_catalogue_order(self):
        a = RUN.parse_args(['b', 'o'])
        self.assertEqual(a.cases, ['positive', 'wrong-post', 'all-infeasible'])

    def test_explicit_selection_keeps_order(self):
        a = RUN.parse_args(['b', 'o', '--cases', 'all-infeasible', 'positive'])
        self.assertEqual(a.cases, ['all-infeasible', 'positive'])

    def test_single_case(self):
        a = RUN.parse_args(['b', 'o', '--cases', 'wrong-post'])
        self.assertEqual(a.cases, ['wrong-post'])

    def test_duplicate_rejected_before_output(self):
        with self.assertRaises(SystemExit):
            RUN.parse_args(['b', 'o', '--cases', 'positive', 'positive'])

    def test_unknown_case_rejected(self):
        with self.assertRaises(SystemExit):
            RUN.parse_args(['b', 'o', '--cases', 'bogus'])


class BuildCommandTests(unittest.TestCase):
    def test_exact_command_no_trailing_dot(self):
        cmd = RUN.build_command('IMG', '/work-root', '/out/cases/positive',
                                '/out/results/positive')
        self.assertEqual(len(cmd), 20)
        self.assertEqual(cmd[:4], ['docker', 'run', '--rm', '--network'])
        self.assertEqual(cmd[4], 'none')
        self.assertEqual(cmd[cmd.index('--cpus') + 1], '2')
        self.assertEqual(cmd[cmd.index('--memory') + 1], '2g')
        self.assertEqual(cmd[cmd.index('--entrypoint') + 1], 'bash')
        self.assertIn('-v', cmd)
        self.assertIn('/work-root:/work:ro', ' '.join(cmd))
        self.assertIn('/out/cases/positive:/cases:ro', ' '.join(cmd))
        self.assertIn('/out/results/positive:/results', ' '.join(cmd))
        self.assertEqual(cmd[-3], 'IMG')
        self.assertEqual(cmd[-2], '-c')
        script = cmd[-1]
        self.assertTrue(script.endswith('--proc=answer --lemma=CheckChoice\n'))
        self.assertNotIn('CheckChoice .', script)
        self.assertIn('timeout --verbose -k 5 45', script)
        self.assertIn('gillian_js.exe', script)

    def test_command_matches_script_constant(self):
        self.assertEqual(RUN.build_command('i', 'a', 'b', 'c')[-1], RUN.DOCKER_SCRIPT)


class FreshOutputRootTests(unittest.TestCase):
    def test_existing_empty_dir_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'out'
            out.mkdir()
            with self.assertRaises(SystemExit):
                RUN.ensure_fresh_output_root(out)
            self.assertTrue(out.is_dir())
            self.assertEqual(list(out.iterdir()), [])

    def test_existing_nonempty_dir_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'out'
            out.mkdir()
            (out / 'old').mkdir()
            with self.assertRaises(SystemExit):
                RUN.ensure_fresh_output_root(out)

    def test_missing_dir_created(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'nested' / 'out'
            RUN.ensure_fresh_output_root(out)
            self.assertTrue(out.is_dir())


class StagedExecutedTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.staged = self.tmp / 'case.gil'
        self.staged.write_bytes(b'FIXTURE-BYTES')
        self.executed = self.tmp / 'results' / 'case.gil'
        self.executed.parent.mkdir()
        self.executed.write_bytes(b'FIXTURE-BYTES')

    def tearDown(self):
        self._tmp.cleanup()

    def test_matching_succeeds(self):
        self.assertEqual(RUN.verify_staged_executed(self.staged, self.executed), [])

    def test_changed_bytes_fail(self):
        self.executed.write_bytes(b'DIFFERENT')
        problems = RUN.verify_staged_executed(self.staged, self.executed)
        self.assertEqual(len(problems), 1)
        self.assertIn('differ', problems[0])

    def test_missing_executed_fails(self):
        self.executed.unlink()
        problems = RUN.verify_staged_executed(self.staged, self.executed)
        self.assertEqual(len(problems), 1)
        self.assertIn('missing', problems[0])

    def test_symlinked_executed_fails(self):
        self.executed.unlink()
        self.executed.symlink_to(self.staged)
        problems = RUN.verify_staged_executed(self.staged, self.executed)
        self.assertEqual(len(problems), 1)
        self.assertIn('symlink', problems[0])

    def test_symlinked_staged_fails(self):
        real = self.tmp / 'real.gil'
        real.write_bytes(b'FIXTURE-BYTES')
        self.staged.unlink()
        self.staged.symlink_to(real)
        problems = RUN.verify_staged_executed(self.staged, self.executed)
        self.assertEqual(len(problems), 1)
        self.assertIn('symlink', problems[0])


class PinMismatchesTests(unittest.TestCase):
    def test_modified_non_binary_pin_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            target = p / 'smt.ml'
            target.write_text('let x = 1\n')
            pin_map_path = p / 'pins.json'
            real_sha = RUN.file_sha(target)
            pin_map_path.write_text(json.dumps(
                {str(target): real_sha},
                indent=2) + '\n')
            map_sha = RUN.file_sha(pin_map_path)
            # No drift, map present: clean (only the listed smt.ml pin is
            # checked; the fixture map lists no missing files).
            self.assertEqual(RUN.pin_mismatches(pin_map_path, map_sha), [])
            # Drift a NON-BINARY pinned file. The MAP bytes/hash are
            # unchanged, so this is a FILE mismatch, not a map mismatch.
            target.write_text('let x = 2\n')
            problems = RUN.pin_mismatches(pin_map_path, map_sha)
            paths = [p0[0] for p0 in problems]
            self.assertIn(str(target), paths)
            self.assertNotIn(str(pin_map_path), paths)

    def test_missing_pinned_file_is_mismatch_not_exception(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            target = p / 'smt.ml'
            target.write_text('let x = 1\n')
            pin_map_path = p / 'pins.json'
            pin_map_path.write_text(json.dumps(
                {str(target): RUN.file_sha(target),
                 str(p / 'absent.ml'): '1' * 64},
                indent=2) + '\n')
            map_sha = RUN.file_sha(pin_map_path)
            problems = RUN.pin_mismatches(pin_map_path, map_sha)
            self.assertEqual(problems, [[str(p / 'absent.ml'), None, '1' * 64]])

    def test_pin_map_rewritten_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            pin_map_path = p / 'pins.json'
            pin_map_path.write_text('{}\n')
            map_sha = RUN.file_sha(pin_map_path)
            self.assertEqual(RUN.pin_mismatches(pin_map_path, map_sha), [])
            pin_map_path.write_text('{"rewritten": "0"}\n')
            problems = RUN.pin_mismatches(pin_map_path, map_sha)
            self.assertEqual(len(problems), 1)
            self.assertEqual(problems[0][0], str(pin_map_path))
            self.assertEqual(problems[0][2], map_sha)


    def test_main_exits_before_any_subprocess_on_drifted_source_pin(self):
        # Real main() against tiny temp fixtures: the binary check passes,
        # then the early pin gate must sys.exit before ANY subprocess call.
        # A stub/no-op pin gate leaves subprocess.run reachable and this
        # test fails.
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            backend = base / 'backend'
            bin_path = backend / '_build' / 'default' / 'Gillian-JS' / 'bin' / 'gillian_js.exe'
            bin_path.parent.mkdir(parents=True)
            bin_path.write_bytes(b'BIN')
            src = base / 'smt.ml'
            src.write_text('let x = 1\n')
            map_path = base / 'frozen-backend.json'
            pin_map = {str(bin_path): RUN.file_sha(bin_path),
                       str(src): RUN.file_sha(src)}
            map_path.write_text(json.dumps(pin_map, indent=2) + '\n')
            out_root = base / 'out'  # main() creates it; pre-existing dirs rejected
            inv_path = base / 'inventory.py'
            inv_path.write_text('# fake inventory helper\n')
            fake_inv = types.SimpleNamespace(
                sha=RUN.file_sha,
                snapshot=lambda groups: {'files': [], 'links': {}},
                assert_unchanged=lambda *a: None)
            with mock.patch.object(RUN, 'INVENTORY_PATH', str(inv_path)), \
                 mock.patch.object(RUN, 'INVENTORY_SHA', RUN.file_sha(inv_path)), \
                 mock.patch.object(RUN, 'FROZEN_BACKEND_JSON', str(map_path)), \
                 mock.patch.object(RUN, 'FROZEN_BACKEND_SHA', RUN.file_sha(map_path)), \
                 mock.patch.object(RUN, 'load_inventory', lambda: fake_inv), \
                 mock.patch.object(RUN.subprocess, 'run') as fake_run:
                src.write_text('let x = 2\n')  # drift the NON-BINARY pin
                with self.assertRaises(SystemExit) as ctx:
                    RUN.main([str(backend), str(out_root)])
                fake_run.assert_not_called()
                self.assertIn('frozen pin mismatches', str(ctx.exception))
                self.assertIn(str(src), str(ctx.exception))


class PostcheckFailureFlowTests(unittest.TestCase):
    """Unit fixture only: a fake producer + a raising assert_unchanged.
    Verifies a handled postcheck failure stops the next case while the first
    raw receipt (producer.json / output.bin / output.log) is retained."""

    def test_postcheck_failure_stops_next_case_keeps_first_receipt(self):
        class FakeInv:
            @staticmethod
            def sha(path):
                return RUN.file_sha(path)

            @staticmethod
            def snapshot(groups):
                return {'files': [{'path': g['path'], 'sha256': 'x',
                                    'role': g['role']} for g in groups], 'links': {}}

            @staticmethod
            def assert_unchanged(groups, before):
                raise ValueError('fixture: frozen input drifted')

        class FakeProc:
            stdout = b'Verifying lemma CheckChoice... s Success\n' \
                     b'Verifying one spec of procedure answer... s Success\n' \
                     b'All total procedure specs succeeded\n'
            stderr = b''
            returncode = 0

        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            fixture_dir = base / 'fixtures'
            fixture_dir.mkdir()
            for name in RUN.CASES:
                (fixture_dir / f'{name}.gil').write_text(f'FIX {name}\n')
            output_root = base / 'out'
            output_root.mkdir()
            (output_root / 'cases').mkdir()
            (output_root / 'results').mkdir()
            inv = FakeInv()
            before = inv.snapshot(RUN.source_groups(fixture_dir, base, base / 'bin'))
            reports, receipts = {}, []

            def fake_producer(cmd, *a, **kw):
                # Mimic DOCKER_SCRIPT's `cp /cases/case.gil .` into /results,
                # then write the verbose log the way the real producer does.
                src = next(c.rsplit(':', 2)[0] for c in cmd if c.endswith(':/cases:ro'))
                dst = next(c.rsplit(':', 2)[0] for c in cmd if c.endswith(':/results'))
                Path(dst, 'case.gil').write_bytes(Path(src, 'case.gil').read_bytes())
                (Path(dst) / 'file.log').write_text(
                    'Results of unfolding Choice(n):\n'
                    '  final state non admissible\n')
                return FakeProc()

            with mock.patch.object(RUN.subprocess, 'run',
                                   side_effect=fake_producer) as fake_run, \
                 mock.patch.object(RUN.shutil, 'disk_usage',
                                   return_value=types.SimpleNamespace(free=2**40)), \
                 mock.patch.object(RUN, 'pin_mismatches', return_value=[]):
                halted, disk_b, disk_a = RUN.run_selected_cases(
                    RUN.CASES, fixture_dir, 'IMG', base, output_root, inv,
                    [], before, reports, receipts)
            # The producer mock must be the fake, not a real command.
            self.assertEqual(fake_run.call_count, 1)
            self.assertTrue(halted.startswith('positive: postchecks failed'))
            # First case: receipt + raw outputs retained, report recorded.
            pos_results = output_root / 'results' / 'positive'
            self.assertTrue((pos_results / 'producer.json').is_file())
            self.assertTrue((pos_results / 'output.bin').is_file())
            self.assertTrue((pos_results / 'output.log').is_file())
            self.assertTrue((pos_results / 'report.json').is_file())
            # The raw receipt must still point at the preserved verbose log.
            self.assertEqual(receipts[0]['verboseLog'],
                             str(pos_results / 'file.log'))
            self.assertIsNotNone(receipts[0]['verboseLogSha256'])
            self.assertTrue((pos_results / 'file.log').is_file())
            self.assertEqual(receipts[0]['rawOutputBytes'],
                             len(FakeProc.stdout) + len(FakeProc.stderr))
            self.assertIsNone(receipts[0]['signal'])
            report_pos = reports['positive']
            # The streams genuinely classified positive (positive verdicts in
            # raw stdout, both verbose markers in file.log), but the injected
            # inventory failure must force controlPassed false. A no-op report
            # correction leaves controlPassed true and this test fails.
            self.assertFalse(report_pos['controlPassed'])
            self.assertFalse(report_pos['certificationReady'])
            self.assertFalse(report_pos['inputsUnchanged'])
            self.assertIsNotNone(report_pos['checksFailed'])
            self.assertFalse(report_pos['proofAccepted'])
            self.assertFalse(report_pos['fullProofDone'])
            report_on_disk = json.loads(
                (pos_results / 'report.json').read_text())
            self.assertFalse(report_on_disk['controlPassed'])
            # Second case never started; both remaining cases skipped.
            self.assertEqual(reports['wrong-post']['status'], 'skipped')
            self.assertFalse((output_root / 'results' / 'wrong-post').exists())
            self.assertEqual(reports['all-infeasible']['status'], 'skipped')
            self.assertEqual(fake_run.call_count, 1)

    def test_control_failure_stops_next_case_keeps_first_receipt(self):
        class FakeInv:
            @staticmethod
            def sha(path):
                return RUN.file_sha(path)

            @staticmethod
            def snapshot(groups):
                return {'files': [{'path': g['path'], 'sha256': 'x',
                                    'role': g['role']} for g in groups], 'links': {}}

            @staticmethod
            def assert_unchanged(groups, before):
                return None

        class FakeProc:
            stdout = b'Segmenta' b'tion fault (core dumped)\n'  # hard failure
            stderr = b''
            returncode = 139

        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            fixture_dir = base / 'fixtures'
            fixture_dir.mkdir()
            for name in RUN.CASES:
                (fixture_dir / f'{name}.gil').write_text(f'FIX {name}\n')
            output_root = base / 'out'
            output_root.mkdir()
            (output_root / 'cases').mkdir()
            (output_root / 'results').mkdir()
            inv = FakeInv()
            before = inv.snapshot(RUN.source_groups(fixture_dir, base, base / 'bin'))
            reports, receipts = {}, []
            def fake_producer(cmd, *a, **kw):
                # Mimic DOCKER_SCRIPT's `cp /cases/case.gil .` into /results.
                src = next(c.rsplit(':', 2)[0] for c in cmd if c.endswith(':/cases:ro'))
                dst = next(c.rsplit(':', 2)[0] for c in cmd if c.endswith(':/results'))
                Path(dst, 'case.gil').write_bytes(Path(src, 'case.gil').read_bytes())
                return FakeProc()

            with mock.patch.object(RUN.subprocess, 'run',
                                   side_effect=fake_producer), \
                 mock.patch.object(RUN.shutil, 'disk_usage',
                                   return_value=types.SimpleNamespace(free=2**40)), \
                 mock.patch.object(RUN, 'pin_mismatches', return_value=[]):
                halted, disk_b, disk_a = RUN.run_selected_cases(
                    RUN.CASES, fixture_dir, 'IMG', base, output_root, inv,
                    [], before, reports, receipts)
            self.assertTrue(halted.startswith('positive: control did not pass'))
            self.assertTrue((output_root / 'results' / 'positive' / 'producer.json')
                            .is_file())
            receipt = json.loads((output_root / 'results' / 'positive'
                                  / 'producer.json').read_text())
            self.assertEqual(receipt['returncode'], 139)
            self.assertIsNone(receipt['signal'])
            report_pos = reports['positive']
            self.assertFalse(report_pos['controlPassed'])
            self.assertTrue(report_pos['inputsUnchanged'])
            self.assertIsNone(report_pos['checksFailed'])
            self.assertEqual(reports['wrong-post']['status'], 'skipped')
            self.assertEqual(reports['all-infeasible']['status'], 'skipped')

    def test_disk_floor_rejects_before_any_producer(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            fixture_dir = base / 'fixtures'
            fixture_dir.mkdir()
            for name in RUN.CASES:
                (fixture_dir / f'{name}.gil').write_text(f'FIX {name}\n')
            output_root = base / 'out'
            output_root.mkdir()
            (output_root / 'cases').mkdir()
            (output_root / 'results').mkdir()

            class FakeInv:
                @staticmethod
                def sha(path):
                    return RUN.file_sha(path)

                @staticmethod
                def snapshot(groups):
                    return {'files': [], 'links': {}}

                @staticmethod
                def assert_unchanged(groups, before):
                    return None

            tiny = types.SimpleNamespace(free=1)
            with mock.patch.object(RUN.shutil, 'disk_usage', return_value=tiny):
                with mock.patch.object(RUN.subprocess, 'run') as fake_run:
                    with self.assertRaises(SystemExit) as ctx:
                        RUN.run_selected_cases(
                            RUN.CASES, fixture_dir, 'IMG', base, output_root,
                            FakeInv(), [], [], {}, [])
                fake_run.assert_not_called()
            self.assertIn('insufficient free disk', str(ctx.exception))


class _FixtureBase:
    """Build the small temp fixture tree the case/finalization tests share."""

    def _make(self, tmp):
        base = Path(tmp)
        fixture_dir = base / 'fixtures'
        fixture_dir.mkdir()
        for name in RUN.CASES:
            (fixture_dir / f'{name}.gil').write_text(f'FIX {name}\n')
        output_root = base / 'out'
        output_root.mkdir()
        (output_root / 'cases').mkdir()
        (output_root / 'results').mkdir()
        return base, fixture_dir, output_root


class MetadataExceptionTests(_FixtureBase, unittest.TestCase):
    """A completed producer (passing streams) followed by an OPTIONAL
    metadata failure: the raw receipt survives, the case is forced failed,
    and the next case is never invoked."""

    def _running_fake(self):
        class FakeInv:
            @staticmethod
            def sha(path):
                return RUN.file_sha(path)

            @staticmethod
            def snapshot(groups):
                return {'files': [{'path': g['path'], 'sha256': 'x',
                                    'role': g['role']} for g in groups],
                        'links': {}}

            @staticmethod
            def assert_unchanged(groups, before):
                return None

        class FakeProc:
            stdout = (b'Verifying lemma CheckChoice... s Success\n'
                      b'Verifying one spec of procedure answer... s Success\n'
                      b'All total procedure specs succeeded\n')
            stderr = b''
            returncode = 0

        def fake_producer(cmd, *a, **kw):
            src = next(c.rsplit(':', 2)[0]
                       for c in cmd if c.endswith(':/cases:ro'))
            dst = next(c.rsplit(':', 2)[0]
                       for c in cmd if c.endswith(':/results'))
            Path(dst, 'case.gil').write_bytes(
                Path(src, 'case.gil').read_bytes())
            (Path(dst) / 'file.log').write_text(
                'Results of unfolding Choice(n):\n'
                '  final state non admissible\n')
            return FakeProc()

        return FakeInv, FakeProc, fake_producer

    def test_metadata_exception_retains_receipt_and_stops(self):
        FakeInv, FakeProc, fake_producer = self._running_fake()
        with tempfile.TemporaryDirectory() as tmp:
            base, fixture_dir, output_root = self._make(tmp)
            inv = FakeInv()
            before = inv.snapshot(
                RUN.source_groups(fixture_dir, base, base / 'bin'))
            reports, receipts = {}, []

            # Make the OPTIONAL verbose-hash step raise after the producer.
            def raising_sha(path):
                if str(path).endswith('file.log'):
                    raise OSError('fixture: verbose hash failed')
                return RUN.file_sha(path)

            with mock.patch.object(RUN.subprocess, 'run',
                                   side_effect=fake_producer) as fake_run, \
                 mock.patch.object(RUN.shutil, 'disk_usage',
                                   return_value=types.SimpleNamespace(
                                       free=2 ** 40)), \
                 mock.patch.object(inv, 'sha', raising_sha), \
                 mock.patch.object(RUN, 'pin_mismatches', return_value=[]):
                halted, disk_b, disk_a = RUN.run_selected_cases(
                    RUN.CASES, fixture_dir, 'IMG', base, output_root, inv,
                    [], before, reports, receipts)

            # Only ONE producer ran; the later cases were never invoked.
            self.assertEqual(fake_run.call_count, 1)
            self.assertTrue(halted.startswith('positive: metadata capture failed'))
            pos = output_root / 'results' / 'positive'
            # Raw receipt survives intact.
            self.assertTrue((pos / 'producer.json').is_file())
            self.assertTrue((pos / 'output.bin').is_file())
            self.assertTrue((pos / 'output.log').is_file())
            self.assertTrue((pos / 'file.log').is_file())
            receipt = json.loads((pos / 'producer.json').read_text())
            self.assertEqual(receipt['returncode'], 0)
            self.assertIsNone(receipt['signal'])
            self.assertEqual(len(receipt['command']),
                             len(RUN.build_command('IMG', base, base, base)))
            self.assertIsNotNone(receipt['elapsedSeconds'])
            self.assertIsNotNone(receipt['rawOutputSha256'])
            self.assertEqual(receipt['rawOutputBytes'],
                             len(FakeProc.stdout) + len(FakeProc.stderr))
            self.assertIsNotNone(receipt['metadataError'])
            self.assertIn('verbose hash failed', receipt['metadataError'])
            self.assertIn('stagedInventory', receipt)
            self.assertIn('stagedGroup', receipt)
            # Case report is forced failed and carries the collected reason.
            rep = reports['positive']
            self.assertFalse(rep['controlPassed'])
            self.assertFalse(rep['certificationReady'])
            self.assertFalse(rep['proofAccepted'])
            self.assertFalse(rep['fullProofDone'])
            self.assertIsNotNone(rep['checksFailed'])
            self.assertIn('verbose hash failed', rep['checksFailed'])
            self.assertTrue((pos / 'report.json').is_file())
            report_on_disk = json.loads((pos / 'report.json').read_text())
            self.assertFalse(report_on_disk['controlPassed'])
            # Next case never started.
            self.assertEqual(reports['wrong-post']['status'], 'skipped')
            self.assertFalse(
                (output_root / 'results' / 'wrong-post').exists())
            self.assertEqual(reports['all-infeasible']['status'], 'skipped')
            self.assertEqual(fake_run.call_count, 1)


class FinalizationTests(unittest.TestCase):
    """Use the real inventory implementation over tiny files and symlinks."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.out = self.base / 'out'
        self.out.mkdir()
        self.source = self.base / 'source.gil'
        self.source.write_text('source before\n')
        self.groups = [{'role': 'fixture-source', 'kind': 'file', 'path': str(self.source)}]
        self.inv = RUN.load_inventory()
        self.before = self.inv.snapshot(self.groups)
        RUN.write_json(self.out / 'input-inventory.json',
                       {'groups': self.groups, 'snapshot': self.before})
        self.pin_map = self.base / 'pins.json'
        RUN.write_json(self.pin_map, {str(self.source): RUN.file_sha(self.source)})
        for name, value in [('FROZEN_BACKEND_JSON', str(self.pin_map)),
                            ('FROZEN_BACKEND_SHA', RUN.file_sha(self.pin_map))]:
            patch = mock.patch.object(RUN, name, value)
            patch.start()
            self.addCleanup(patch.stop)
        self.raw = self.out / 'output.bin'
        self.raw.write_bytes(b'raw process output\n')
        self.receipt = self.out / 'producer.json'
        self.receipt.write_bytes(b'{"returncode":0,"signal":null}\n')
        (self.out / 'retained-link').symlink_to('output.bin')
        self.reports = {'positive': {'controlPassed': True, 'inputsUnchanged': True}}
        self.receipts = [{'case': 'positive', 'returncode': 0, 'signal': None}]

    def finish(self, selected=('positive',), run_failed=None):
        raw, receipt = self.raw.read_bytes(), self.receipt.read_bytes()
        result = RUN.finalize_run(self.out, self.inv, self.groups, self.before,
                                 self.reports, self.receipts, 'IMG', 'BIN',
                                 selected, None, 2**40, 2**40, run_failed)
        self.assertEqual(self.raw.read_bytes(), raw)
        self.assertEqual(self.receipt.read_bytes(), receipt)
        self.assertTrue((self.out / 'worker-result.json').is_file())
        self.assertTrue((self.out / 'retained-files.json').is_file())
        for key in ('proofAccepted', 'certificationReady', 'fullProofDone'):
            self.assertIs(result[3][key], False)
        return result

    def test_success_records_real_file_link_hashes_and_groups(self):
        code, halted, error, worker = self.finish()
        self.assertEqual(code, 0)
        self.assertIsNone(halted)
        self.assertIsNone(error)
        inventory = json.loads((self.out / 'retained-files.json').read_text())
        self.assertTrue(inventory['complete'])
        self.assertEqual(inventory['snapshot']['links'],
                         {str(self.out / 'retained-link'): 'output.bin'})
        files = {x['path']: x['sha256'] for x in inventory['snapshot']['files']}
        self.assertNotIn(str(self.out / 'retained-files.json'), files)
        for path, digest in files.items():
            self.assertEqual(RUN.file_sha(path), digest)
        self.assertIn(str(self.out / 'worker-result.json'), files)
        self.assertEqual(json.loads((self.out / 'input-inventory.json').read_text())['groups'],
                         self.groups)

    def test_final_pin_and_snapshot_drift_rejects(self):
        self.source.write_text('changed\n')
        code, _, _, worker = self.finish()
        self.assertNotEqual(code, 0)
        self.assertFalse(worker['inputsUnchangedAfter'])
        self.assertTrue(worker['pinDriftProblems'])

    def test_missing_pin_map_retains_failure_evidence(self):
        self.pin_map.unlink()
        code, _, _, worker = self.finish()
        self.assertNotEqual(code, 0)
        self.assertFalse(worker['inputsUnchangedAfter'])
        self.assertIsNone(worker['frozenBackendJsonSha256'])
        self.assertIn('final pin check failed', worker['finalPinReason'])

    def test_final_snapshot_exception_retains_evidence(self):
        snapshot = self.inv.snapshot
        def fail_inputs(groups):
            if groups == self.groups:
                raise OSError('input snapshot unavailable')
            return snapshot(groups)
        with mock.patch.object(self.inv, 'snapshot', side_effect=fail_inputs):
            code, _, error, worker = self.finish()
        self.assertNotEqual(code, 0)
        self.assertIsNone(error)
        self.assertFalse(worker['inputsUnchangedAfter'])
        self.assertIn('input snapshot unavailable', worker['finalSnapshotReason'])

    def test_broken_evidence_link_retains_incomplete_inventory(self):
        (self.out / 'retained-link').unlink()
        (self.out / 'retained-link').symlink_to('missing-file')
        code, halted, error, worker = self.finish()
        self.assertNotEqual(code, 0)
        self.assertIn('run-evidence snapshot failed', error)
        self.assertIn(error, halted)
        self.assertFalse(worker['evidenceComplete'])
        self.assertFalse(json.loads((self.out / 'retained-files.json').read_text())['complete'])

    def test_unexecuted_selected_case_never_passes(self):
        code, _, _, _ = self.finish(selected=RUN.CASES)
        self.assertNotEqual(code, 0)

    def test_failed_case_never_passes(self):
        self.reports['positive']['controlPassed'] = False
        code, _, _, _ = self.finish()
        self.assertNotEqual(code, 0)

    def test_unverified_case_inputs_never_pass(self):
        self.reports['positive']['inputsUnchanged'] = False
        code, _, _, _ = self.finish()
        self.assertNotEqual(code, 0)

    def test_main_finalizes_later_system_exit(self):
        # Exercise the actual main-to-finalizer path; only image inspection and
        # producer execution are mocked. File receipts/inventories are real.
        backend = self.base / 'backend'
        binary = backend / '_build/default/Gillian-JS/bin/gillian_js.exe'
        binary.parent.mkdir(parents=True)
        binary.write_bytes(b'BIN')
        RUN.write_json(self.pin_map, {str(binary): RUN.file_sha(binary)})
        output = self.base / 'fresh-output'
        def stopped_run(*args):
            result = output / 'results' / 'positive'
            result.mkdir()
            (result / 'output.bin').write_bytes(b'completed raw')
            (result / 'producer.json').write_text('{"returncode":0}\n')
            args[-1].append({'case': 'positive', 'returncode': 0})
            raise SystemExit('insufficient free disk before next producer')
        with mock.patch.object(RUN, 'FROZEN_BACKEND_SHA', RUN.file_sha(self.pin_map)), \
             mock.patch.object(RUN, 'source_groups', return_value=self.groups), \
             mock.patch.object(RUN.subprocess, 'run',
                               return_value=types.SimpleNamespace(stdout=RUN.IMAGE_ID)) as image, \
             mock.patch.object(RUN, 'run_selected_cases', side_effect=stopped_run):
            with self.assertRaises(SystemExit) as raised:
                RUN.main([str(backend), str(output), '--cases', 'positive', 'wrong-post'])
        self.assertEqual(raised.exception.code, 3)
        image.assert_called_once()
        self.assertEqual(json.loads((output / 'worker-result.json').read_text())['executedCases'],
                         ['positive'])
        self.assertEqual((output / 'results/positive/output.bin').read_bytes(), b'completed raw')
        self.assertTrue((output / 'retained-files.json').is_file())


def main():
    unittest.main(verbosity=2)


if __name__ == '__main__':
    main()
