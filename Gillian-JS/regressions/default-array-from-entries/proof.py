#!/usr/bin/env python3
"""Check the actual two-entry runtime body; discard bounded RAM diagnostics."""
import argparse, collections, json, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from run import file_sha, runtime_sha, sha

HERE = Path(__file__).resolve().parent
CASES = ('positive', 'wrong-post', 'wrong-value', 'alias', 'wrong-descriptor',
         'wrong-order', 'changed-frame', 'constant-rank', 'missing-rank',
         'registered-positive', 'registered-wrong-post', 'registered-alias', 'registered-unchecked')
ARGS = 'iterable,#emd,#p,#pmd,#s,#smd,#payload,#payloadMd,REVERSE'

def specification(name, wrong=False, ready=False):
    inputs = 'FEInput('+ARGS.replace('REVERSE','#reverse').replace('iterable,','#entries,',1)+')'
    fresh = '(!(ret == iterable)) * (!(ret == #p)) * (!(ret == #s)) * (!(ret == #payload))'
    if wrong: fresh = fresh.replace('(!(ret == iterable))', '(ret == iterable)', 1)
    types='types(#entries:Obj,#emd:Obj,#p:Obj,#pmd:Obj,#s:Obj,#smd:Obj,#payload:Obj,#payloadMd:Obj,#reverse:Bool)'
    # One union PRE; eager unfolding retains both complete order alternatives.
    registration='FEReadyBinding(#objectMd,#functionMd) * ' if ready else ''
    extra_types='types(#objectMd:Obj,#functionMd:Obj) * ' if ready else ''
    return ('spec '+name+'(xsc,vthis,iterable)\n[[ (iterable == #entries) * '+types+' * '+extra_types+registration+inputs+' ]]\n'
        '[[ '+registration+inputs+' * FEPrefix(ret,2,#payload,#reverse) * '+fresh+' ]] variant(as_int 0) normal\n')

def prepare(case, runtime, variant):
    obj = (runtime/'JS2JSIL/Object.jsil').read_text()
    original = obj
    spec = specification('Object_fromEntries',wrong=variant=='wrong-post')
    start = 'proc Object_fromEntries (xsc, vthis, iterable) {'
    assert obj.count(start) == 1
    obj = obj.replace(start, spec+start, 1)
    invariant = ('\n          invariant (FEInput('+ARGS.replace('REVERSE','#reverse')+') * '
        'FEPrefix(out,index,#payload,#reverse) * (len == 2) * types(index:Num) * '
        '(is-int index) * (0 <=# index) * (index <=# 2)) [bind: index]'
        ' variant(as_int (2 - index));\n'
        '          unfold FEPrefix(out,index,#payload,#reverse);')
    head = 'fe_loop: PHI(index: zero, next_index);'
    assert obj.count(head) == 1
    if variant == 'constant-rank': invariant = invariant.replace('as_int (2 - index)', 'bool_to_int true')
    if variant == 'missing-rank': invariant = invariant.replace(' variant(as_int (2 - index))', '')
    obj = obj.replace(head, head+invariant, 1)
    fault = ''
    if variant == 'wrong-value': fault = '\n          [out,"payload"] := {{"d",undefined,true,true,true}};'
    if variant == 'alias': fault = '\n          ret := iterable;'
    if variant in ('wrong-descriptor', 'wrong-order'):
        fault = '\n          saved := [out,"payload"];'
        if variant == 'wrong-descriptor':
            fault += '\n          value := l-nth(saved,1);\n          [out,"payload"] := {{"d",value,true,false,true}};'
        else: fault += '\n          delete(out,"payload");\n          [out,"payload"] := saved;'
    if variant == 'changed-frame':
        fault = '\n          pair := "get" (iterable,"0") with elab;\n          [pair,"0"] := {{"d","FRAME corrupted",true,true,true}};'
    end = 'fe_done: ret := out;'
    assert obj.count(end) == 1
    obj = obj.replace(end, end+fault, 1)
    # Body changes are confined to these declared proof commands/spec and fault.
    restored = obj.replace(spec+start,start,1).replace(head+invariant,head,1)
    if fault: restored = restored.replace(end+fault,end,1)
    assert restored == original
    (case/'Object.jsil').write_text(obj)
    (case/'Init.jsil').write_bytes((runtime/'JS2JSIL/Init.jsil').read_bytes())
    (case/'Effects.gil').write_bytes((HERE/'Effects.gil').read_bytes())
    (case/'entry.js').write_text('/* @import Object.jsil */\n/* @import Effects.gil */\nvar unused = 0;\n')
    if variant.startswith('registered-'):
        caller=specification('FERegistered',wrong=variant=='registered-wrong-post',ready=True)
        caller+='''proc FERegistered(xsc,vthis,iterable) {
  fn := "get" ($lobj,"fromEntries") with err;
  md := metadata(fn);
  fid := [md,"@call"];
  scp := [md,"@scope"];
  ret := fid(scp,$lobj,iterable) with err;
  return;
  err: throw
};
'''
        if variant=='registered-alias': caller=caller.replace('  return;','  ret := iterable;\n  return;',1)
        (case/'Registered.jsil').write_text(caller)
        (case/'Registration.gil').write_bytes((HERE/'Registration.gil').read_bytes())
        (case/'entry.js').write_text('/* @import Object.jsil */\n/* @import Effects.gil */\n'
            '/* @import Registered.jsil */\n/* @import Registration.gil */\nvar unused = 0;\n')
    return dict(runtimeBodySHA256=sha(original.encode()), preparedSHA256=sha(obj.encode()))

def observe(case, output):
    counts = collections.Counter(); dispatch = {}; answers = {}; succeeded = []; failed = []; post = []
    hard = []
    log = case/'file.log'
    if log.exists():
      with log.open('rb') as stream:
        for raw in stream:
          assert len(raw) <= 1024*1024, 'log line cap'
          line = raw.decode(errors='backslashreplace').strip()
          if line.startswith('SMT_PRIMARY_CHECK_DISPATCH '):
            m = re.fullmatch(r'SMT_PRIMARY_CHECK_DISPATCH query=(query_\d+\.smt2) command=(.*)',line)
            assert m and m[1] not in dispatch and m[2]=='(check-sat)' and len(dispatch)<4096
            dispatch[m[1]] = m[2]
          if line.startswith('SMT_QUERY_RESULT '):
            row = dict(x.split('=',1) for x in line.split()[1:])
            assert set(row)=={'query','caller','raw_unknown','timeout_ms','phase_selection','result'}
            # raw_unknown selects the API's exception policy; result is the
            # actual SMT answer (smt.ml exec_sat'/run_sat). Reject UNKNOWN below.
            assert row['raw_unknown'] in ('true','false') and row['phase_selection']=='3' and 0<int(row['timeout_ms'])<=30000,'SMT result metadata'
            assert row['query'] in dispatch and row['query'] not in answers,'SMT result lacks unique dispatch'
            answers[row['query']] = row['result']; counts[row['result']] += 1
          m = re.search(r'VERIFICATION SUCCESS: Spec (\S+) \((\d+),\s*(\d+)\)',line)
          if m: succeeded.append([m[1],int(m[2]),int(m[3])])
          m = re.search(r'VERIFICATION FAILURE in spec (\S+) \((\d+),\s*(\d+)\): (.*)',line)
          if m:
            failed.append([m[1],int(m[2]),int(m[3])]);
            if "Couldn't satisfy postcondition" in m[4]: post.append(failed[-1])
          if re.search(r'The solver returned: unknown|Internal error!|Parser Error|Uncaught exception|Invalid_argument|Fatal error: exception|Out_of_memory|VACUOUS|NATIVE_EXECUTION_FAILURE',line):
            hard.append(line[:300]); assert len(hard) <= 8
    files = {p.name for p in (case/'gillian_smt_queries').glob('query_*.smt2')}
    assert set(dispatch) == set(answers) == files, 'complete query/dispatch/answer join'
    assert not counts['unknown'] and set(counts) <= {'sat','unsat'}, 'indefinite SMT answer'
    return dict(queries=len(answers), answers=dict(counts), successes=succeeded, failures=failed,
        postFailures=post, hard=hard,
        symbolicTests=list(map(int,re.findall(r'Obtained (\d+) symbolic test',output))))

def main(args):
    selected = args.cases.split(',') if args.cases else list(CASES)
    assert selected and len(set(selected)) == len(selected) and set(selected) <= set(CASES)
    runtime = args.runtime.resolve(); before = runtime_sha(runtime)
    result = dict(controlsPassed=False, capabilityQualified=False, proofAccepted=False, fullProofDone=False,
        binarySHA256=file_sha(args.binary), runtimeSHA256=before, methodSHA256=file_sha(__file__),
        contractSHA256=file_sha(HERE/'Effects.gil'),registrationSHA256=file_sha(HERE/'Registration.gil'), rows=[])
    try:
      with tempfile.TemporaryDirectory(prefix='from-entries-proof-',dir='/dev/shm') as tmp:
        for name in selected:
          case = Path(tmp)/name; case.mkdir(); row=dict(name=name,passed=False);result['rows'].append(row)
          row.update(prepare(case,runtime,name))
          inputs={p.name:file_sha(p) for p in case.iterdir()}
          row['inputSHA256']=sha(json.dumps(inputs,sort_keys=True,separators=(',',':')).encode())
          registered=name.startswith('registered-'); unchecked=name=='registered-unchecked'
          argv=[str(args.binary),'verify',str(case/'entry.js'),'--total',
                *([] if unchecked else ['--proc=Object_fromEntries']),
                *(['--proc=FERegistered'] if registered else []),
                *(['--proof-dependency=FERegistered:Object_fromEntries'] if registered and not unchecked else []),
                '--logging=verbose','--dump-smt']
          for directory in (case,runtime/'JS2JSIL',runtime/'JSLogic',runtime/'JSON'): argv += ['-R',str(directory)]
          began=time.monotonic()
          try:
            run=subprocess.run(argv,cwd=case,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
            raw=run.stdout;rc=run.returncode;timed_out=False
          except subprocess.TimeoutExpired as error: raw=error.stdout or b'';rc=-9;timed_out=True
          row['native']=dict(returncode=rc,signal=-rc if rc<0 else None,timedOut=timed_out,
              seconds=round(time.monotonic()-began,4),stdoutSHA256=sha(raw),stdoutBytes=len(raw))
          row['inputsUnchanged']=all(file_sha(case/name)==digest for name,digest in inputs.items())
          assert row['inputsUnchanged']
          assert len(raw)<=262144,'stdout cap'
          text=re.sub(r'\x1b\[[0-9;]*m','',raw.decode(errors='backslashreplace'))
          row['observation']=observe(case,text)
          obs=row['observation']; assert not timed_out and not obs['hard'], text[-1000:]
          ids={('Object_fromEntries',0,0),('Object_fromEntries',1,0)}
          if registered:
            caller_ids={('FERegistered',0,0),('FERegistered',1,0)}
            if unchecked:
              diagnostic='Unsupported totality proof: Object_fromEntries has not passed every totality proof case in this run.'
              assert rc==124 and text.count(diagnostic)==1 and obs['symbolicTests']==[2] and not obs['successes'] and not obs['failures'] and text.count('Verifying one spec of procedure FERegistered...')==1 and 'Verifying one spec of procedure Object_fromEntries...' not in text and 'All total procedure specs succeeded' not in text,text[-1200:]
            elif name=='registered-positive':
              assert rc==0 and {tuple(x) for x in obs['successes']}==ids|caller_ids and len(obs['successes'])==4 and not obs['failures'] and obs['symbolicTests']==[4] and text.count('All total procedure specs succeeded')==1,text[-1200:]
            else:
              assert rc==1 and {tuple(x) for x in obs['successes']}==ids and len(obs['successes'])==2 and {tuple(x) for x in obs['postFailures']}==caller_ids and len(obs['postFailures'])==2 and obs['failures']==obs['postFailures'] and obs['symbolicTests']==[4] and 'All total procedure specs succeeded' not in text,text[-1200:]
          elif name=='positive': assert rc==0 and {tuple(x) for x in obs['successes']}==ids and len(obs['successes'])==2 and not obs['failures'] and obs['symbolicTests']==[2] and text.count('All total procedure specs succeeded')==1, text[-1200:]
          elif name=='missing-rank':
            expected='Unsupported totality proof: Object_fromEntries has a control-flow cycle without a ranked invariant header.'
            assert rc==124 and text.count(expected)==1 and not obs['symbolicTests'] and not obs['successes'] and not obs['queries'],text[-1000:]
          elif name=='constant-rank': assert rc==1 and text.count('Loop variant is not a strictly smaller natural integer')>=1 and not obs['successes'],text[-1000:]
          else:
            expected=1 if name=='wrong-order' else 2
            assert rc==1 and len(obs['postFailures'])==expected and obs['failures']==obs['postFailures'] and len(obs['successes'])==2-expected and {tuple(x) for x in obs['successes']+obs['postFailures']}==ids and obs['symbolicTests']==[2] and 'All total procedure specs succeeded' not in text,text[-1200:]
          row['passed']=True;shutil.rmtree(case)
      result['runtimeUnchanged']=runtime_sha(runtime)==before
      result['controlsPassed']=len(result['rows'])==len(selected) and all(r['passed'] for r in result['rows']) and result['runtimeUnchanged']
    except Exception as error: result['error']=str(error)[-1500:]
    data=json.dumps(result,separators=(',',':'));assert len(data.encode())<=16384;print(data)
    return 0 if result['controlsPassed'] else 3

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--binary',type=Path,required=True)
    p.add_argument('--runtime',type=Path,required=True);p.add_argument('--cases')
    raise SystemExit(main(p.parse_args()))
