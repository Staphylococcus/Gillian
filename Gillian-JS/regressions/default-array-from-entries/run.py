#!/usr/bin/env python3
"""Concrete registered-path calibration; not quantified capability acceptance."""
import argparse, hashlib, json, os, re, selectors, shutil, subprocess, tempfile, time
from pathlib import Path

CASES = ('payload-first', 'status-first', 'empty-payload-first', 'empty-status-first',
         'wrong-value', 'alias', 'wrong-descriptor', 'wrong-order', 'changed-frame', 'missing-binding')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for part in iter(lambda: f.read(65536), b''): h.update(part)
    return h.hexdigest()

def runtime_sha(root):
    # In-memory correspondence only; no inventory or source snapshot is written.
    return sha(json.dumps([(str(p.relative_to(root)), file_sha(p))
        for p in sorted(root.rglob('*')) if p.suffix in ('.jsil', '.gil')],
        separators=(',', ':')).encode())

def program(reverse=False, empty=False):
    value = json.dumps([] if empty else [" A ", "A", "A", chr(0xD800)])
    order = '[second, first]' if reverse else '[first, second]'
    first, second = ('statusCode', 'payload') if reverse else ('payload', 'statusCode')
    return ('''"use strict";
var payload = VALUE;
var first = ["payload", payload], second = ["statusCode", 200];
var entries = ORDER;
if (typeof Object.fromEntries !== "function") throw "FE_CHECK:binding";
var answer = Object.fromEntries(entries);
if (answer === entries || answer === first || answer === second || answer === payload)
  throw "FE_CHECK:freshness";
if (answer.payload !== payload || answer.statusCode !== 200) throw "FE_CHECK:value";
var pd = Object.getOwnPropertyDescriptor(answer, "payload");
var sd = Object.getOwnPropertyDescriptor(answer, "statusCode");
if (!pd || !sd || pd.value !== payload || sd.value !== 200 ||
    !pd.writable || !pd.enumerable || !pd.configurable ||
    !sd.writable || !sd.enumerable || !sd.configurable) throw "FE_CHECK:descriptor";
var keys = Object.keys(answer);
if (keys.length !== 2 || keys[0] !== "FIRST" || keys[1] !== "SECOND") throw "FE_CHECK:order";
if (entries.length !== 2 || first.length !== 2 || second.length !== 2 ||
    first[0] !== "payload" || first[1] !== payload ||
    second[0] !== "statusCode" || second[1] !== 200) throw "FE_CHECK:frame";
if (Object.getPrototypeOf(answer) !== Object.prototype) throw "FE_CHECK:prototype";
"FE_CHECK:ok";
'''.replace('VALUE', value).replace('ORDER', order)
        .replace('FIRST', first).replace('SECOND', second)).encode()

def mutate(name, obj, init):
    store = '[out, entry_key] := {{"d", entry_value, true, true, true}};'
    edits = {
      'wrong-value': (store, store.replace('entry_value', 'undefined')),
      'alias': ('out := "create_default_object" ($lobj_proto, "Object", true);', 'out := iterable;'),
      'wrong-descriptor': (store, store.replace('true, true, true', 'true, false, true')),
      'wrong-order': ('index_key := "i__toString" (index)', 'index_key := "i__toString" (len - 1 - index)'),
      'changed-frame': (store, store + '\n          [entry, "0"] := {{"d", "FE damaged", true, true, true}};')}
    if name == 'missing-binding':
        line = '[$lobj, "fromEntries"]              := {{ "d", $lobj_fromEntries, true, false, true }};'
        assert init.count(line) == 1
        return obj, init.replace(line, '', 1)
    if name in edits:
        old, new = edits[name]; assert obj.count(old) == 1 and new not in obj
        changed = obj.replace(old, new, 1); assert changed.replace(new, old, 1) == obj
        return changed, init
    assert name in CASES[:4]
    return obj, init

def run(argv, cwd, seconds):
    start = time.monotonic()
    output = bytearray(); stop = None
    with subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as p:
      with selectors.DefaultSelector() as sel:
        os.set_blocking(p.stdout.fileno(), False); sel.register(p.stdout, selectors.EVENT_READ)
        while True:
          if time.monotonic() - start >= seconds: stop = 'timeout'; break
          for key, _ in sel.select(0.02):
            data = os.read(key.fd, 8192)
            if not data: sel.unregister(key.fileobj); continue
            output.extend(data)
            if len(output) > 256*1024: stop = 'concrete output cap'; break
          if stop or (p.poll() is not None and not sel.get_map()): break
      if stop: p.kill()
      rc = p.wait(timeout=5)
    return rc, bytes(output), round(time.monotonic() - start, 4), stop

def main(args):
    selected = args.cases.split(',') if args.cases else list(CASES)
    assert selected and len(set(selected)) == len(selected) and set(selected) <= set(CASES)
    root = args.runtime.resolve(); obj = (root/'JS2JSIL/Object.jsil').read_text()
    init = (root/'JS2JSIL/Init.jsil').read_text(); before = runtime_sha(root)
    result = dict(calibrationPassed=False, capabilityQualified=False, proofAccepted=False,
        fullProofDone=False, binarySHA256=file_sha(args.binary), runtimeSHA256=before,
        methodSHA256=file_sha(__file__), rows=[])
    expected = dict(zip(CASES[4:], ('value', 'freshness', 'descriptor', 'order', 'frame', 'binding')))
    try:
      with tempfile.TemporaryDirectory(prefix='from-entries-', dir='/dev/shm') as tmp:
        tmp = Path(tmp)
        for name in selected:
          case = tmp/name; case.mkdir(); row = dict(name=name, passed=False); result['rows'].append(row)
          code = program('status-first' in name, name.startswith('empty-'))
          (case/'case.js').write_bytes(code)
          if name in CASES[:4]:
            rc, output, elapsed, stop = run([args.node, str(case/'case.js')], case, 15)
            row['host'] = dict(returncode=rc, seconds=elapsed)
            assert not stop and rc == 0 and not output, 'host native calibration failed'
          changed_obj, changed_init = mutate(name, obj, init)
          # Init imports its neighbour Object before searching -R directories.
          (case/'Object.jsil').write_text(changed_obj)
          (case/'Init.jsil').write_text(changed_init)
          argv = [str(args.binary), 'exec', str(case/'case.js'), '--logging=disabled', '--debug', '--no-heap']
          for directory in (case, root/'JS2JSIL', root/'JSLogic', root/'JSON'):
            argv += ['-R', str(directory)]
          rc, output, elapsed, stop = run(argv, case, 20)
          assert (case/'Object.jsil').read_text() == changed_obj
          assert (case/'Init.jsil').read_text() == changed_init
          row['native'] = dict(returncode=rc, signal=-rc if rc < 0 else None, seconds=elapsed,
              resourceStop=stop, stdoutBytes=len(output), stdoutSHA256=sha(output))
          text = re.sub(r'\x1b\[[0-9;]*m', '', output.decode('utf-8', errors='backslashreplace'))
          assert not stop, stop+': '+text[:600]
          assert not re.search(r'Internal error!|Parser Error|Uncaught exception|Assertion failed|Undefined variable', text), text[-1000:]
          assert rc == (1 if name in expected else 0), text[-1000:]
          marker = ('SUCCESSFUL TERMINATION: (error, u16"FE_CHECK:'+expected[name]+'")'
                    if name in expected else 'SUCCESSFUL TERMINATION: (normal, u16"FE_CHECK:ok")')
          assert text.count(marker) == 1, text[-1000:]
          row.update(sourceSHA256=sha(code), passed=True)
          assert sum(p.stat().st_size for p in tmp.rglob('*') if p.is_file()) <= 64*2**20, 'RAM cap'
          shutil.rmtree(case)
      result['runtimeUnchanged'] = runtime_sha(root) == before
      result['calibrationPassed'] = len(result['rows']) == len(selected) and all(r['passed'] for r in result['rows']) and result['runtimeUnchanged']
    except Exception as error:
      result['error'] = str(error)[-1500:]
    data = json.dumps(result, separators=(',', ':')); assert len(data.encode()) <= 16384
    print(data)
    return 0 if result['calibrationPassed'] else 3

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--runtime', type=Path, required=True)
    p.add_argument('--node', required=True); p.add_argument('--cases')
    raise SystemExit(main(p.parse_args()))
