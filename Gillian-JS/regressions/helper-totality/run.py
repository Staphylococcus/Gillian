#!/usr/bin/env python3
"""Require the intended totality result; crashes and timeouts never pass."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
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
    ("runtime-function-layout.js", ["--total", "--proc=builtin"], TOTAL),
    ("runtime-function-layout.js", ["--total", "--proc=builtinConfig"], TOTAL),
    ("runtime-function-layout.js", ["--total", "--proc=builtinFixedWrong"], POST),
    ("runtime-function-layout.js", ["--total", "--proc=userFunction"], TOTAL),
    ("runtime-function-layout.js", ["--total", "--proc=userFixedWrong"], POST),
    ("runtime-function-layout.js", ["--total", "--proc=userArityWrong"], POST),
    ("runtime-function-layout.js", ["--total", "--proc=constructor"], TOTAL),
    ("runtime-function-layout.js", ["--total", "--proc=constructorPlainWrong"], POST),
    ("boolean-negated-wrong.gil", ["--total"], POST),
    ("boolean-negated.gil", ["--total"], TOTAL),
    ("boolean-negated-reversed-wrong.gil", ["--total"], POST),
    ("boolean-negated-reversed.gil", ["--total"], TOTAL),
    ("sep-object.gil", ["--total"], TOTAL),
    ("sep-object-wrong.gil", ["--total"], (1, "Assert failed with argument")),
    ('sep-capture.gil', ["--total", "--proc=answer"], TOTAL),
    ('sep-capture-zero.gil', ["--total", "--proc=answer"], TOTAL),
    ('sep-capture-nan.gil', ["--total", "--proc=answer"], TOTAL),
    ('sep-predicate.gil', ["--total", "--proc=answer"], TOTAL),
    ('sep-capture-wrong.gil', ["--total", "--proc=answer"], (1, "Pure assertion failed")),
    ('sep-missing.gil', ["--total", "--proc=answer"], (1, "Assert failed with argument")),
    ('sep-wrong-cell.gil', ["--total", "--proc=answer"], (1, "Assert failed with argument")),
    ('sep-branch.gil', ["--total", "--proc=answer"], (1, "Assert failed with argument")),
    ('sep-known-predicate.gil', ["--total", "--proc=answer"], (1, "Assert failed with argument")),
    ('sep-shadow.gil', ["--total", "--proc=answer"], (124, "separation assertion binders shadow protected")),
    ('sep-caller-shadow.gil', ["--total", "--proc=answer"], (124, "separation assertion binders shadow protected")),
    ('sep-duplicate.gil', ["--total", "--proc=answer"], (124, "duplicate separation assertion binders")),
    ('sep-unbound.gil', ["--total", "--proc=answer"], (124, "separation assertion binder was not captured")),
    ('sep-js-scope.js', ["--total", "--proc=answer"], TOTAL),
    ('sep-js-scope-wrong.js', ["--total", "--proc=answer"], (1, "Assert failed with argument")),
    ('expanded-finite.gil', ['--total', '--proc=answer'], TOTAL),
    ('expanded-finite-wrong.gil', ['--total', '--proc=answer'], POST),
    ('expanded-budget.gil', ['--total', '--proc=answer'], (124, "totality proof is incomplete")),
    ('expanded-unbounded.gil', ['--total', '--proc=answer'], (124, "totality proof is incomplete")),
    ('expanded-leaf-fault.gil', ['--total', '--proc=answer'], (1, "Pure assertion failed")),
    ('expanded-mutual.gil', ['--total', '--proc=answer'], TOTAL),
    ('expanded-dynamic.gil', ['--total', '--proc=answer'], TOTAL),
    ('expanded-heap.gil', ['--total', '--proc=answer'], TOTAL),
    ('expanded-heap-wrong.gil', ['--total', '--proc=answer'], POST),
    ('expanded-nested-loop.gil', ['--total', '--proc=answer'], TOTAL),
    ('expanded-nested-loop-wrong.gil', ['--total', '--proc=answer'], POST),

    ("cold-loop.gil", ["--total", "--proc=answer"], TOTAL),
    ("reached-loop.gil", ["--total", "--proc=answer"], (124, "control-flow cycle without a ranked invariant header")),
    ("symbolic-loop.gil", ["--total", "--proc=answer"], (124, "control-flow cycle without a ranked invariant header")),
    ("second-loop.gil", ["--total", "--proc=answer"], (124, "control-flow cycle without a ranked invariant header")),
    ("twice-cold-loop.gil", ["--total", "--proc=answer"], TOTAL),
    ("cold-irreducible.gil", ["--total", "--proc=answer"], TOTAL),
    ("reached-irreducible-one.gil", ["--total", "--proc=answer"], (124, "control-flow cycle without a ranked invariant header")),
    ("reached-irreducible-two.gil", ["--total", "--proc=answer"], (124, "control-flow cycle without a ranked invariant header")),
    ("javascript-empty-assert.js", ["--total", "--proc=answer"], (1, "Pure assertion failed")),
    ("javascript-empty-assert.js", ["--proc=answer"], (1, "Pure assertion failed")),
    ("javascript-empty-assert-true.js", ["--total", "--proc=answer"], TOTAL),
    ("javascript-empty-assert-true.js", ["--proc=answer"], PARTIAL),
    ("helper-terminal-assume.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-terminal-assume-reached.gil", ["--total", "--proc=answer"], (124, "operation outside the totality fragment")),
    ("javascript-call-wrong.js", ["--total", "--proc=answer"], POST),
    ("dynamic-branches.gil", ["--total", "--proc=answer"], TOTAL),
    ("dynamic-wrong-branch.gil", ["--total", "--proc=answer"], (1, "Couldn't satisfy postcondition")),
    ("dynamic-cycle.gil", ["--total", "--proc=answer"], (124, "unranked inlined call cycle")),
    ("dynamic-unresolved.gil", ["--total", "--proc=answer"], (124, "dynamic call target is not resolved")),
    ("dynamic-invalid.gil", ["--total", "--proc=answer"], (1, "EProc")),
    ("dynamic-no-rank.gil", ["--total", "--proc=answer"], (124, "has no checked entry measure")),
    ("dynamic-stuck.gil", ["--total", "--proc=answer"], (1, "variant is not a strictly smaller natural integer")),
    ("javascript-call.js", ["--total", "--proc=answer"], TOTAL),
    ("lemma-recursive-false.gil", ["--total"], (124, "has not passed every lemma proof case")),
    ("lemma-checked.gil", ["--total"], TOTAL),
    ("lemma-omitted.gil", ["--total", "--procs-only"], (124, "has not passed every lemma proof case")),
    ("lemma-assume.gil", ["--total"], (124, "proof operation outside the totality fragment")),
    ("lemma-false.gil", ["--total"], (124, "has not passed every lemma proof case")),
    ("lemma-axiom.gil", ["--total"], (124, "requires a nonempty checked lemma proof")),
    ("lemma-macro-cycle.gil", ["--total"], (124, "cyclic macro expansion")),
    ("lemma-produce.gil", ["--total"], (124, "proof operation outside the totality fragment")),
    ("lemma-empty-pre.gil", ["--total"], (124, "requires a nonempty checked lemma proof")),
    ("lemma-caller.gil", ["--total"], TOTAL),
    ("lemma-recursive.gil", ["--total"], TOTAL),
    ("lemma-no-descent.gil", ["--total"], (124, "has not passed every lemma proof case")),

    ("helper-ranked.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-twice.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-error.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-error-wrong.gil", ["--total", "--proc=answer"], POST),
    ("helper-branch-fault.gil", ["--total", "--proc=answer"], (1, "MIFLoc(null)")),
    ("macro-lemma.gil", ["--total", "--proc=answer"], (124, "has not passed every lemma proof case")),
    ("helper-summary-arity.gil", ["--total", "--proc=answer", "--proc=value"], (124, "requires exact call arity")),

    ("inline.gil", ["--total", "--proc=answer"], TOTAL),
    ("wrong-body.gil", ["--total", "--proc=answer"], POST),
    ("imported-false.gil", ["--total", "--proc=answer"], POST),
    ("helper-assume.gil", ["--total", "--proc=answer"], (124, "operation outside the totality fragment")),
    ("helper-cycle.gil", ["--total", "--proc=answer"], (124, "unranked inlined call cycle")),
    ("helper-mutual.gil", ["--total", "--proc=answer"], (124, "unranked inlined call cycle")),
    ("helper-loop.gil", ["--total", "--proc=answer"], (124, "control-flow cycle")),
    ("helper-action.gil", ["--total", "--proc=answer"], (124, "uncertified primitive action")),
    ("helper-dynamic.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-duplicate.gil", ["--total", "--proc=answer"], (124, "duplicate formal parameters")),
    ("helper-missing-arg.gil", ["--total", "--proc=answer"], TOTAL),
    ("helper-extra-arg.gil", ["--total", "--proc=answer"], TOTAL),
    ("macro-if.gil", ["--total", "--proc=answer"], TOTAL),
    ("macro-false.gil", ["--total", "--proc=answer"], (1, "Pure assertion failed: false")),
    ("macro-assume.gil", ["--total", "--proc=answer"], (124, "proof operation outside the totality fragment")),
    ("macro-cycle.gil", ["--total", "--proc=answer"], (124, "cyclic proof macro expansion")),
    ("macro-dead-assume.gil", ["--total", "--proc=answer"], TOTAL),
    ("javascript-return.js", ["--total", "--proc=answer"], TOTAL),
    ("javascript-empty.js", ["--total", "--proc=answer"], TOTAL),
    ("javascript-wrong.js", ["--total", "--proc=answer"], POST),
]

if __name__ == "__main__":
    output = Path(tempfile.mkdtemp(prefix="gillian-helper-totality-",
                                  dir=os.environ.get("GILLIAN_RESULTS_ROOT")))
    results = []
    for index, (file, options, expected) in enumerate(CASES):
        source = ROOT / file
        directory = output / f"{index:02d}-{source.stem}"
        directory.mkdir()
        for dependency in ["imported.gil", "runtime-function-layout.gil"]:
            shutil.copy2(ROOT / dependency, directory / dependency)
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
