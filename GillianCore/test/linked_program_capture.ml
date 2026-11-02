open Gillian
open Utils
open Gil_syntax
module C = Gil_syntax.Linked_program_capture
module K = C.Codec
module W = C.Writer
let check b why = Alcotest.(check bool) why true b
let rejects f = match (try f ();None with e->Some e) with
  |None->Alcotest.fail "incomplete/corrupt capture unexpectedly accepted" |Some _->()
let json_roundtrip json =
  let restored=K.untag(Yojson.Safe.from_string(Yojson.Safe.to_string(K.tag json))) in
  check (K.equal json restored) "lossless tree"
let floats () =
  List.iter(fun bits->json_roundtrip(`Float(Int64.float_of_bits bits)))
    [0L;Int64.min_int;1L;0x000fffffffffffffL;0x0010000000000000L;
     0x7ff0000000000000L;0xfff0000000000000L;0x7ff8000000000001L;0x7ff8000000000011L];
  check(not(K.equal(`Float 0.)(`Float(-0.))))"signed-zero corruption";
  check(not(K.equal(`Float(Int64.float_of_bits 0x7ff8000000000001L))
    (`Float(Int64.float_of_bits 0x7ff8000000000011L))))"NaN payload corruption"
let bytes () =
  let raw=String.init 256 Char.chr in
  json_roundtrip(`Assoc[raw,`String(raw^"\000\"\\");raw,`String "duplicate key"]);
  json_roundtrip(`Tuple[`Int 1;`Float 1.;`Intlit "18446744073709551617"]);
  json_roundtrip(`Variant(raw,Some(`List[`Null;`Bool false])));
  json_roundtrip(`Variant(raw,None));
  check(not(K.equal(`Int 1)(`Float 1.)))"Int/Float constructor corruption"
let literals () =
  let values=[Literal.Num(-0.);Literal.Num(Int64.float_of_bits 0x7ff8000000000011L);
    Literal.Int(Z.of_string("-"^String.make 1000 '9'));
    Literal.Int(Z.of_string(String.make 1000 '9'));
    Literal.String "\000\255\"\\";
    Literal.Utf16String(Utf16.of_canonical(Utf16.of_code_units[0;0xd800;0xdc00;0xdfff;34;92]));
    Literal.Utf16String(Utf16.of_canonical(Utf16.of_code_units[0xd800]))] in
  List.iter(fun value->ignore(K.checked
    ~guard:(K.guard_ast(fun v x->v#visit_literal () x))
    ~to_json:Literal.to_yojson ~of_json:Literal.of_yojson value))values;
  rejects(fun()->ignore(K.checked ~to_json:Literal.to_yojson
    ~of_json:(fun _->Ok(Literal.Int Z.one)) (Literal.Int(Z.of_int 2))))
let budgets () =
  rejects(fun()->K.guard_plain(fun x->x));
  let rec cycle=1::cycle in rejects(fun()->K.guard_plain cycle);
  rejects(fun()->K.guard_plain Int64.max_int);
  rejects(fun()->K.guard_plain(String.make 65537 'x'));
  rejects(fun()->ignore(K.untag(`List[`String "float64";`String "NaN"])));
  rejects(fun()->ignore(K.unhex "0g"));
  let payload=K.checked ~to_json:C.jstring ~of_json:C.string_of_json (String.make 65536 'x') in
  ignore(C.frame_of_json(C.frame_json {C.phase="linked";seq=0;kind="boundary";route=[];payload}));
  let reason f =
    try f ();Alcotest.fail "missing capture budget diagnostic"
    with K.Incomplete why -> why
  in
  let diagnostic expected f =
    Alcotest.(check string) "exact bounded diagnostic" expected (reason f)
  in
  diagnostic
    "value nodes/depth budget nodes=1 node_limit=0 depth=0 depth_limit=512 nodes_exceeded=1 depth_exceeded=0"
    (fun()->ignore(K.inspect ~node_limit:0 0));
  diagnostic
    "value nodes/depth budget nodes=2 node_limit=32768 depth=1 depth_limit=0 nodes_exceeded=0 depth_exceeded=1"
    (fun()->ignore(K.inspect ~depth_limit:0 [0]));
  diagnostic
    "value nodes/depth budget nodes=2 node_limit=1 depth=1 depth_limit=0 nodes_exceeded=1 depth_exceeded=1"
    (fun()->ignore(K.inspect ~node_limit:1 ~depth_limit:0 [0]));
  diagnostic "stage-probe stage=typed-input" (fun()->ignore(K.checked
    ~guard:(fun _->raise(K.Incomplete "stage-probe"))
    ~to_json:C.jint ~of_json:C.int_of_json 0));
  diagnostic "value string budget stage=derived-json" (fun()->ignore(K.checked
    ~to_json:(fun _->`String(String.make 65537 'x')) ~of_json:(fun _->Ok 0) 0));
  let guards=ref 0 in
  diagnostic "stage-probe stage=typed-decoded" (fun()->ignore(K.checked
    ~guard:(fun _->incr guards;if !guards=2 then raise(K.Incomplete "stage-probe"))
    ~to_json:C.jint ~of_json:C.int_of_json 0));
  check(!guards=2)"both typed guards retained";
  let key=String.make 40 '\255' in
  let pred={Pred.pred_name=key;pred_source_path=Some(String.make 65537 'x');
    pred_loc=None;pred_internal=false;pred_num_params=0;pred_params=[];ins_number=0;
    pred_definitions=[];pred_facts=[];pred_guard=None;pred_pure=false;
    pred_abstract=false;pred_nounfold=false;pred_normalised=false} in
  let preds=Hashtbl.create 1 in Hashtbl.add preds key pred;
  let empty ()=Hashtbl.create 1 in
  let prog=Prog.make ~imports:[] ~lemmas:(empty()) ~preds ~funcs:(empty())
    ~datatypes:(empty()) ~only_specs:(empty()) ~procs:(empty()) ~macros:(empty())
    ~bi_specs:(empty()) ~proc_names:[] ~predecessors:(empty()) () and last=ref None in
  let why=reason(fun()->C.iter_program ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase:"post-logic"
    ~emit:(fun frame->last:=Some frame)prog) in
  Alcotest.(check string) "bounded table context"
    ("value string budget stage=typed-input phase=post-logic table=preds keyIndex=0 keyHexPrefix=" ^
     String.make 64 'f' ^ " bindingOrdinal=0") why;
  check(String.length why<=512)"bounded failure context";
  check((match !last with Some(f:C.frame)->
    f.kind="key"&&f.phase="post-logic"&&f.route=["preds";"0";key]|None->false))
    "last key frame retains full raw route"
let fixture () =
  let loc={Location.loc_start={pos_line=3;pos_column=4};loc_end={pos_line=5;pos_column=6};loc_source="origin\000\255"} in
  let anno=Annot.Basic.make ~origin_loc:loc ~loop_info:["a";"a"] () in
  let true_=Expr.Lit(Literal.Bool true) in
  let spec={Spec.spec_name="p";spec_params=["x"];spec_sspecs=[
    {Spec.ss_pre=([Asrt.Pure true_],Some loc);ss_posts=[([Asrt.Emp],Some loc)];ss_variant=None;ss_verifier_scope=None;
     ss_flag=Flag.Normal;ss_to_verify=true;ss_label=Some("L",["x"])}];spec_normalised=false;
    spec_incomplete=false;spec_to_verify=true;spec_location=Some loc} in
  let proc={Proc.proc_name="p";proc_source_path=Some "source\255";proc_internal=true;
    proc_body=[|anno,Some 0,Cmd.Goto 2;
      anno,Some 1,Cmd.PhiAssignment["phi",[Expr.Lit(Literal.Num 0.);Expr.Lit(Literal.Num(-0.))]];
      anno,Some 2,Cmd.GuardedGoto(true_,1,0)|];proc_params=["x"];proc_spec=Some spec;
    proc_aliases=["alias";"alias"];proc_calls=["callee";"callee"];
    proc_display_name=Some("pretty\000","display\255");proc_hidden=true} in
  let singleton key value=let t=Hashtbl.create 1 in Hashtbl.add t key value;t in
  let pred={Pred.pred_name="P";pred_source_path=Some "pred";pred_loc=Some loc;pred_internal=false;
    pred_num_params=1;pred_params=["x",Some Type.ObjectType];ins_number=1;
    pred_definitions=[Some("D",["x"]),[Asrt.Emp]];pred_facts=[true_];pred_guard=Some[Asrt.Emp];
    pred_pure=false;pred_abstract=false;pred_nounfold=false;pred_normalised=false} in
  let lemma={Lemma.lemma_name="L";lemma_source_path=Some "lemma";lemma_internal=false;
    lemma_params=["x"];lemma_specs=[];lemma_proof=Some[LCmd.Assert true_];lemma_variant=None;
    lemma_existentials=["e"];lemma_location=Some loc} in
  let func={Func.func_name="F";func_source_path=Some "function";func_loc=Some loc;
    func_num_params=0;func_params=[];func_definition=Expr.Lit(Literal.Int(Z.of_string "123456789012345678901234567890"))} in
  let datatype={Datatype.datatype_name="D";datatype_source_path=Some "datatype";datatype_loc=Some loc;datatype_constructors=[]} in
  let macro={Macro.macro_name="M";macro_params=["x"];macro_definition=[LCmd.Assume true_]} in
  let bispec={BiSpec.bispec_name="B";bispec_params=["x"];bispec_pres=[([Asrt.Emp],Some loc)];bispec_normalised=false} in
  let prog=Prog.make ~imports:["runtime\255",false;"runtime\255",false]
    ~lemmas:(singleton "L" lemma) ~preds:(singleton "P" pred) ~funcs:(singleton "F" func)
    ~datatypes:(singleton "D" datatype) ~only_specs:(singleton "p" spec)
    ~procs:(singleton "p" proc) ~macros:(singleton "M" macro) ~bi_specs:(singleton "B" bispec)
    ~proc_names:["p";"p"] ~predecessors:(singleton ("p",2,1) 0) () in
  prog,proc
let collect phase prog =
  let out=ref [] in C.iter_program ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase ~emit:(fun f->out:=f:: !out)prog;
  List.rev !out
let structure () =
  let prog,proc=fixture() in
  let original=Proc.to_yojson Annot.Basic.to_yojson C.jint proc in
  let frames=collect "linked" prog in C.validate_frames frames;
  let wire=List.map(fun f->C.frame_of_json(Yojson.Safe.from_string(Yojson.Safe.to_string(C.frame_json f))))frames in
  C.validate_frames wire;
  check(K.equal original(Proc.to_yojson Annot.Basic.to_yojson C.jint proc))"actual input unchanged";
  List.iter(fun name->check(List.exists(fun(f:C.frame)->f.kind="table"&&f.route=[name])frames)("table "^name))C.tables;
  List.iter(fun field->check(List.exists(fun(f:C.frame)->f.kind="proc-field"&&f.route=["procs";"0";"p";"0";field])frames)("field "^field))C.proc_fields;
  let field name=K.untag(List.find(fun(f:C.frame)->f.kind="proc-field"&&f.route=["procs";"0";"p";"0";name])frames).payload in
  List.iter(fun(name,expected)->check(K.equal(field name)expected)("exact proc field "^name))[
    "proc_name",`String "p";"proc_source_path",`String "source\255";"proc_internal",`Bool true;
    "proc_body",`Int 3;"proc_params",`List[`String "x"];
    "proc_spec",(match proc.proc_spec with Some x->Spec.to_yojson x|None->`Null);
    "proc_aliases",`List[`String "alias";`String "alias"];
    "proc_calls",`List[`String "callee";`String "callee"];
    "proc_display_name",`List[`String "pretty\000";`String "display\255"];
    "proc_hidden",`Bool true];
  let predecessor=List.find(fun(f:C.frame)->f.kind="item"&&f.route=["predecessors";"0";"0"])frames in
  check(K.equal(K.untag predecessor.payload)(`List[`String "p";`Int 2;`Int 1;`Int 0]))"raw predecessor tuple";
  let command=List.find(fun(f:C.frame)->f.kind="command"&&f.route=["procs";"0";"p";"0";"proc_body";"1"])frames in
  (match K.untag command.payload with
   |`List[annotation;`Int 1;cmd]->
      check(K.equal annotation(Annot.Basic.to_yojson(let a,_,_=proc.proc_body.(1)in a)))"annotation origin/loop info";
      (match Cmd.of_yojson C.int_of_json cmd with Ok(Cmd.PhiAssignment["phi",[Expr.Lit(Literal.Num p);Expr.Lit(Literal.Num n)]])->
        check(Int64.bits_of_float p=0L&&Int64.bits_of_float n=Int64.min_int)"PHI operand order and zero bits"
       |_->Alcotest.fail "command typed decode")
   |_->Alcotest.fail "ordered annotation/label/command triple");
  check(not(K.equal command.payload(K.tag(`List[`Null;`Int 1;`String "changed command"]))))"command corruption sensitivity"
let framing () =
  let prog,_=fixture() in let frames=collect "post-logic" prog in
  let renumber=List.mapi(fun i(f:C.frame)->{f with seq=i}) in
  rejects(fun()->C.validate_frames(List.tl frames));
  rejects(fun()->C.validate_frames(renumber(List.hd frames::frames)));
  rejects(fun()->C.validate_frames(renumber(List.filter(fun(f:C.frame)->f.kind<>"command"||f.route<>["procs";"0";"p";"0";"proc_body";"1"])frames)));
  let changed=List.map(fun(f:C.frame)->if f.kind="command"then{f with kind="value"}else f)frames in
  rejects(fun()->C.validate_frames changed);
  let a=Array.of_list frames in let x=a.(1)in a.(1)<-a.(2);a.(2)<-x;
  rejects(fun()->C.validate_frames(renumber(Array.to_list a)))
let fresh f =
  let root=Filename.temp_file "linked-capture-control-" "" in Sys.remove root;
  Fun.protect ~finally:(fun()->
      if Sys.file_exists root then (Array.iter(fun name->Sys.remove(Filename.concat root name))(Sys.readdir root);Unix.rmdir root))
    (fun()->f root)
let with_writer ?io ?limit f = fresh(fun root->let w=W.create ?io ?limit root in
  Fun.protect ~finally:(fun()->W.abort w "unit finalizer") (fun()->f root w))
let complete_writer w = W.start w 0;W.write w "{}\n";W.close_phase w;
  W.start w 1;W.write w "{}\n";W.close_phase w;W.finish w "{}\n"
let enabled_same_values () = with_writer(fun root writer->
  let prog,proc=fixture() in
  let before=Proc.to_yojson Annot.Basic.to_yojson C.jint proc in
  let session:C.session={writer;version=1;next=0;counts=[]} in
  C.capture (Some session) ~annot_to_json:Annot.Basic.to_yojson ~annot_of_json:Annot.Basic.of_yojson ~phase:"linked" prog;
  C.capture (Some session) ~annot_to_json:Annot.Basic.to_yojson ~annot_of_json:Annot.Basic.of_yojson ~phase:"post-logic" prog;
  check(K.equal before(Proc.to_yojson Annot.Basic.to_yojson C.jint proc))"same actual program and body values";
  check((List.sort String.compare(Array.to_list(Sys.readdir root))) =
    ["00000000.jsonl";"00000001.jsonl";"00000002.jsonl"])"fixed two phases plus close-required manifest")
let duplicate_bindings () =
  let prog,_=fixture() in
  let pred=Hashtbl.find prog.preds "P" in Hashtbl.add prog.preds "P" {pred with pred_internal=true};
  Hashtbl.add prog.predecessors ("p",2,1) 7;
  let frames=collect "linked" prog in C.validate_frames frames;
  let bindings=List.filter(fun(f:C.frame)->f.kind="value"&&List.hd f.route="preds")frames in
  check(List.length bindings=2)"all duplicate table bindings retained";
  let flags=List.map(fun(f:C.frame)->match K.untag f.payload with `Assoc xs->List.assoc "pred_internal" xs|_->Alcotest.fail "predicate codec")bindings in
  check(flags=[`Bool true;`Bool false])"latest-first predicate stack";
  let rows=List.filter(fun(f:C.frame)->f.kind="item"&&List.hd f.route="predecessors")frames in
  check(List.length rows=2)"all raw predecessor bindings retained";
  check(List.map(fun(f:C.frame)->K.untag f.payload)rows=
    [`List[`String "p";`Int 2;`Int 1;`Int 7];`List[`String "p";`Int 2;`Int 1;`Int 0]])"latest-first predecessor stack"
let writer_success () =
  let io={W.system_io with write=(fun fd b at n->Unix.write fd b at (min n 1))} in
  with_writer ~io(fun _ w->complete_writer w;let failure,sealed,dir,active,_,_,phases,uncertain=W.snapshot w in
    check(failure=None&&sealed&&dir&&active&&phases=3&&not uncertain)"short-write fsync/close complete")
let writer_fault which () =
  let io=match which with
    |"zero"->{W.system_io with write=(fun _ _ _ _->0)}
    |"fsync"->{W.system_io with fsync=(fun _->failwith "injected fsync")}
    |"close"->{W.system_io with close=(fun fd->Unix.close fd;failwith "injected close")}
    |_ ->failwith "fault selector" in
  with_writer ~io(fun _ w->W.start w 0;
    rejects(fun()->W.write w "{}\n";W.close_phase w);
    rejects(fun()->W.write w "retry");
    let failure,_,_,_,_,_,_,_=W.snapshot w in check(failure<>None)"permanent failed latch")
let writer_caps () =
  rejects(fun()->fresh(fun root->ignore(W.create ~limit:67108865L root)));
  with_writer(fun _ w->W.start w 0;rejects(fun()->W.write w(String.make(1024*1024+1)'x')));
  with_writer ~limit:262144L(fun _ w->W.start w 0;rejects(fun()->W.write w(String.make 200000 'x')))
let writer_exclusive () = with_writer(fun root w->
  let file=Filename.concat root "00000000.jsonl" in
  let out=open_out_bin file in output_string out "sentinel";close_out out;
  rejects(fun()->W.start w 0);
  let input=open_in_bin file in let value=really_input_string input 8 in close_in input;
  check(value="sentinel")"exclusive failure preserves existing bytes")
let writer_substitution () =
  let changed=ref false in let io={W.system_io with probe_path=(fun path->
    let a=W.system_io.probe_path path in if !changed then a.(1)<-Int64.succ a.(1);a)}in
  with_writer ~io(fun _ w->changed:=true;rejects(fun()->W.start w 0))
let post_fsync_allocation () =
  let extra=ref 0L in
  let patch a=if a.(7)=0L then a.(3)<-Int64.add a.(3) !extra;a in
  let io={W.system_io with probe_fd=(fun fd->patch(W.system_io.probe_fd fd));
    probe_at=(fun fd name->patch(W.system_io.probe_at fd name));
    fsync=(fun fd->Unix.fsync fd;extra:=4096L)} in
  with_writer ~io(fun _ w->complete_writer w)
let disabled () =
  check(Sys.getenv_opt "GILLIAN_LINKED_PROGRAM_CAPTURE_DIR"=None)"unit method must clear capture env";
  C.with_session(fun session->
    check(session=None)"disabled session";
    C.capture session ~annot_to_json:(fun _->Alcotest.fail "disabled conversion")
      ~annot_of_json:(fun _->Alcotest.fail "disabled decode") ~phase:"linked" (Obj.magic(fun()->())) )
let v2_derived () =
  let json=`List(List.init 32(fun _->`List(List.init 256(fun _->`Int 0)))) in
  let to_json n=if n=7 then json else `Null in
  let of_json value=if K.equal value json then Ok 7 else Error "witness tree" in
  let rejected=try ignore(K.checked ~to_json ~of_json 7);"accepted" with K.Incomplete why->why in
  check(String.starts_with ~prefix:"value nodes/depth budget nodes=32769" rejected &&
    String.ends_with ~suffix:"stage=derived-json" rejected)"V1 derived-only node rejection";
  let payload=K.checked ~version:2 ~to_json ~of_json 7 in
  check(K.equal(K.untag payload)json)"V2 exact complete generic tree";
  rejects(fun()->ignore(K.checked ~version:2 ~to_json ~of_json:(fun _->Ok 8) 7))
let v2_phases () = with_writer(fun root writer->
  let prog,proc=fixture() in
  let pred=Hashtbl.find prog.preds "P" in Hashtbl.add prog.preds "P" {pred with pred_internal=true};
  Hashtbl.add prog.predecessors ("p",2,1) 7;
  let before=Proc.to_yojson Annot.Basic.to_yojson C.jint proc in
  let session:C.session={writer;version=2;next=0;counts=[]} in
  List.iter(fun phase->C.capture(Some session) ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase prog)["linked";"post-logic"];
  let remaining=ref(1024*1024) in
  let files=List.map(fun name->
    let input=open_in_bin(Filename.concat root name) in
    let raw=Fun.protect ~finally:(fun()->close_in input)(fun()->
      let bytes=in_channel_length input in
      check(bytes>0&&bytes<= !remaining)"bounded native fixture files";
      remaining:= !remaining-bytes;really_input_string input bytes) in
    name,raw)["00000000.jsonl";"00000001.jsonl";"00000002.jsonl"] in
  let read_json name=
    let raw=List.assoc name files in
    check(String.ends_with ~suffix:"\n" raw)"fixture complete final LF";
    String.sub raw 0 (String.length raw-1) |> String.split_on_char '\n' |>
      List.map Yojson.Safe.from_string in
  List.iteri(fun index phase->
    let wire=read_json(Printf.sprintf "%08d.jsonl" index) in
    let frames=List.map(C.frame_of_json ~version:2)wire in
    C.validate_frames ~version:2 frames;
    check(List.for_all(fun json->match json with `Assoc(("schema",`Int 2)::_)->true|_->false)wire)
      "every native V2 envelope";
    (match K.untag(List.hd frames).payload with
     |`List[`String "linked-program-capture-single-frame-v2";`String abi;`String words;`String endian]->
       check(abi=Sys.ocaml_version&&words=string_of_int Sys.word_size&&endian=string_of_bool Sys.big_endian)
         "V2 policy and exact native ABI"
     |_->Alcotest.fail "V2 native header");
    let inherited=collect phase prog in
    check(List.length inherited=List.length frames)"single-frame counts unchanged";
    List.iter2(fun(a:C.frame)(b:C.frame)->
      check(a.seq=b.seq&&a.kind=b.kind&&a.route=b.route&&a.phase=b.phase)"same sequence kind route phase";
      if a.kind<>"header" then check(K.equal a.payload b.payload)"unchanged semantic payload/digest input")inherited frames;
    rejects(fun()->ignore(C.frame_of_json(List.hd wire)));
    rejects(fun()->C.validate_frames frames);
    rejects(fun()->C.validate_frames ~version:2(List.tl frames))) ["linked";"post-logic"];
  check(read_json "00000002.jsonl"=[`Assoc[
    "schema",`Int 2;"codecPolicy",`String "linked-program-capture-single-frame-v2";
    "phaseFiles",`List[`String "00000000.jsonl";`String "00000001.jsonl"];
    "frameCounts",`List(List.map(fun n->`Int n)session.counts);
    "requiresNativeSuccessAndClosedWriter",`Bool true;"proofAccepted",`Bool false]])"exact V2 closed manifest";
  check(K.equal before(Proc.to_yojson Annot.Basic.to_yojson C.jint proc))"V2 native actual body unchanged";
  List.iter(fun literal->ignore(K.checked ~version:2
    ~guard:(K.guard_ast(fun v x->v#visit_literal () x))
    ~to_json:Literal.to_yojson ~of_json:Literal.of_yojson literal))
    [Literal.Num(-0.);Literal.Num(Int64.float_of_bits 0x7ff8000000000011L);
     Literal.Utf16String(Utf16.of_canonical(Utf16.of_code_units[0xd800;0;0xdfff]));
     Literal.Int(Z.of_string "123456789012345678901234567890")];
  let artifact="V2_CAPTURE_FIXTURE=" ^ Yojson.Safe.to_string
    (`Assoc(List.map(fun(name,raw)->name,`String raw)files)) in
  check(String.length artifact+1<=1024*1024)"bounded machine-readable native fixture line";
  Printf.printf "%s\n%!" artifact)
let v2_negotiation () =
  check(C.version_of_policy None=1 && C.version_of_policy(Some "linked-program-capture-v1")=1)
    "absent and explicit V1 remain default";
  check(C.version_of_policy(Some "linked-program-capture-single-frame-v2")=2)"explicit V2 only";
  List.iter(fun policy->rejects(fun()->ignore(C.version_of_policy(Some policy))))
    ["";"2";"linked-program-capture-v2";"linked-program-capture-single-frame-v2 "];
  let prog,_=fixture() in
  let frame={C.phase="linked";seq=0;kind="value";route=[];payload=K.tag(`Int 0)} in
  List.iter(fun version->
    rejects(fun()->ignore(K.checked ~version ~to_json:C.jint ~of_json:C.int_of_json 0)))[-1;0;4];
  List.iter(fun version->
    rejects(fun()->ignore(C.frame_json ~version frame));
    rejects(fun()->ignore(C.frame_of_json ~version(C.frame_json frame)));
    rejects(fun()->C.validate_frames ~version []);
    rejects(fun()->C.iter_program ~version ~annot_to_json:Annot.Basic.to_yojson
      ~annot_of_json:Annot.Basic.of_yojson ~phase:"linked" ~emit:(fun _->())prog))[-1;0;6];
  rejects(fun()->ignore(C.frame_of_json ~version:2(C.frame_json frame)))
let v2_limits () =
  let constant value=ignore(K.checked ~version:2 ~to_json:(fun _->`Null) ~of_json:(fun _->Ok value)value) in
  rejects(fun()->constant(fun x->x));let rec cycle=1::cycle in rejects(fun()->constant cycle);
  rejects(fun()->constant Int64.max_int);rejects(fun()->constant(String.make 65537 'x'));
  rejects(fun()->constant(Array.make 262144 0.));
  rejects(fun()->constant(List.init 5(fun _->String.make 65536 'x')));
  let wide n=`List(List.init n(fun _->`List(List.init 256(fun _->`Int 0)))) in
  rejects(fun()->constant(wide 32));
  rejects(fun()->constant(List.init 513 Fun.id));
  rejects(fun()->ignore(K.checked ~version:2 ~to_json:C.jstring
    ~of_json:(fun _->Ok(String.make 65537 'x')) "small"));
  rejects(fun()->ignore(K.checked ~version:2
    ~guard:(K.guard_ast(fun v x->v#visit_literal () x))
    ~to_json:Literal.to_yojson ~of_json:Literal.of_yojson(Literal.Int(Z.shift_left Z.one 65536))));
  let reason json=try ignore(K.checked ~version:2 ~to_json:(fun _->json) ~of_json:(fun _->Ok 0) 0);
    Alcotest.fail "missing V2 bound" with K.Incomplete why->why in
  check(String.ends_with ~suffix:"stage=derived-json"(reason(wide 128)))"whole raw transport guard";
  check(String.ends_with ~suffix:"stage=tagged-payload"(reason(wide 64)))"whole tagged guard before first serialize";
  check(reason(`List(List.init 17(fun _->`String(String.make 65536 'x'))))=
    "value string budget stage=derived-json")"aggregate raw strings";
  check(reason(`String(String.make 262145 'x'))="raw string budget")"unchanged hex ceiling";
  check(reason(`List(List.init 128(fun _->`String(String.make 4090 'x'))))=
    "encoded fragment1MiB cap")"unchanged complete payload byte ceiling";
  rejects(fun()->ignore(C.frame_json ~version:2
    {C.phase="linked";seq=0;kind="value";route=[];payload=K.tag(wide 64)}))
let incomplete_reason f =
  try f ();Alcotest.fail "missing capture rejection"
  with K.Incomplete why->why
let crossing_expr rows columns =
  Expr.EList(List.init rows(fun _->Expr.EList(List.init columns(fun _->Expr.Lit(Literal.Bool true)))))
let visit_expr v x = v#visit_expr () x
let v3_typed_crossing () =
  let value=crossing_expr 32 256 in
  (* Source-derived counts: (4*256+3)*32+2=32866 typed occurrences,
     57506 words, depth292; standard tagged payload624076 ASCII bytes. *)
  ignore(K.inspect ~node_limit:32866 value);
  rejects(fun()->ignore(K.inspect ~node_limit:32865 value));
  List.iter(fun version->
    let conversions=ref 0 in
    let why=incomplete_reason(fun()->ignore(C.ast ~version visit_expr
      (fun x->incr conversions;Expr.to_yojson x) Expr.of_yojson value)) in
    check(!conversions=0&&String.ends_with ~suffix:"stage=typed-input" why)
      "V1/V2 reject the real typed crossing before conversion") [1;2];
  (* Expose the masked V2 transport failure with the same real converters;
     this supplements, and never substitutes for, the full V3 roundtrip. *)
  let why=incomplete_reason(fun()->ignore(K.checked ~version:2
    ~guard:(K.guard_ast_v3 visit_expr) ~to_json:Expr.to_yojson ~of_json:Expr.of_yojson value)) in
  check(String.ends_with ~suffix:"stage=derived-json" why)"old transport bound is independently load-bearing";
  let encoded=C.ast ~version:3 visit_expr Expr.to_yojson Expr.of_yojson value in
  let restored=match Expr.of_yojson(K.untag encoded)with Ok x->x|Error e->Alcotest.fail e in
  check(K.equal(Expr.to_yojson value)(Expr.to_yojson restored))"V3 complete real typed roundtrip";
  let payload=Yojson.Safe.to_string encoded in
  Alcotest.(check int)"standard payload source byte count"624076(String.length payload);
  let frame={C.phase="post-logic";seq=0;kind="value";route=["preds";"0";"crossing";"0"];payload=encoded} in
  let wire=Yojson.Safe.to_string(C.frame_json ~version:3 frame)^"\n" in
  check(String.length wire<=1024*1024)"complete envelope remains within1MiB";
  let decoded=C.frame_of_json ~version:3(Yojson.Safe.from_string wire) in
  check(K.equal decoded.payload encoded)"exact full frame roundtrip";
  rejects(fun()->ignore(C.frame_of_json ~version:2(Yojson.Safe.from_string wire)))
let v3_phases () = with_writer(fun root writer->
  let prog,proc=fixture() and value=crossing_expr 32 256 in
  let original_pred=Hashtbl.find prog.preds "P" in
  let pred={original_pred with pred_facts=[value]} in
  let annotation,_,_=proc.proc_body.(0) in
  let proc={proc with proc_body=[|annotation,Some 0,Cmd.Logic(LCmd.Assert value)|]} in
  Hashtbl.replace prog.preds "P" pred;Hashtbl.replace prog.procs "p" proc;
  let reject_old ()=List.iter(fun version->rejects(fun()->C.iter_program ~version
    ~annot_to_json:Annot.Basic.to_yojson ~annot_of_json:Annot.Basic.of_yojson
    ~phase:"post-logic" ~emit:(fun _->())prog))[1;2] in
  reject_old();
  Hashtbl.replace prog.preds "P" original_pred;reject_old(); (* Command triple alone crosses. *)
  Hashtbl.replace prog.preds "P" pred;
  let before=Proc.to_yojson Annot.Basic.to_yojson C.jint proc in
  let session:C.session={writer;version=3;next=0;counts=[]} in
  List.iter(fun phase->C.capture(Some session) ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase prog)["linked";"post-logic"];
  let read_file name=let input=open_in_bin(Filename.concat root name)in
    Fun.protect ~finally:(fun()->close_in input)(fun()->
      let n=in_channel_length input in check(n>0&&n<=8*1024*1024)"bounded fixture stream";
      really_input_string input n)in
  let names=["00000000.jsonl";"00000001.jsonl";"00000002.jsonl"]in
  let files=List.map(fun name->name,read_file name)names in
  let read name=List.assoc name files in
  List.iteri(fun index phase->
    let text=read(Printf.sprintf "%08d.jsonl" index) in
    let wire=String.sub text 0(String.length text-1)|>String.split_on_char '\n'|>List.map Yojson.Safe.from_string in
    let frames=List.map(C.frame_of_json ~version:3)wire in C.validate_frames ~version:3 frames;
    let big=List.filter(fun(f:C.frame)->f.kind="command"||(f.kind="value"&&List.hd f.route="preds"))frames in
    check(List.length big=2&&List.for_all(fun(f:C.frame)->String.length(Yojson.Safe.to_string f.payload)>600000)big)
      "both whole predicate and command cross without omission";
    (match K.untag(List.hd frames).payload with
     |`List[`String "linked-program-capture-bounded-v3";`String abi;`String words;`String endian]->
        check(abi=Sys.ocaml_version&&words=string_of_int Sys.word_size&&endian=string_of_bool Sys.big_endian)"V3 ABI header"
     |_->Alcotest.fail("V3 header "^phase));
    rejects(fun()->C.validate_frames ~version:2 frames)) ["linked";"post-logic"];
  let manifest=Yojson.Safe.from_string(read "00000002.jsonl") in
  check(manifest=`Assoc["schema",`Int 3;"codecPolicy",`String "linked-program-capture-bounded-v3";
    "phaseFiles",`List[`String "00000000.jsonl";`String "00000001.jsonl"];
    "frameCounts",`List(List.map(fun n->`Int n)session.counts);
    "requiresNativeSuccessAndClosedWriter",`Bool true;"proofAccepted",`Bool false])"exact V3 closed manifest";
  check(K.equal before(Proc.to_yojson Annot.Basic.to_yojson C.jint proc))"actual command/AST unmodified";
  let failure,sealed,dir,active,_,_,phases,uncertain=W.snapshot writer in
  check(failure=None&&sealed&&dir&&active&&phases=3&&not uncertain)"export only closed complete writer";
  let raw_bytes=ref 0 and export_bytes=ref 0 in
  let exports=List.map(fun(name,text)->
    check(String.ends_with ~suffix:"\n" text)"native export preserves final LF";
    let lines=String.sub text 0(String.length text-1)|>String.split_on_char '\n' in
    let prefix="V3_CAPTURE_LINE="^name^":"in
    List.iter(fun line->
      check(String.length line>0&&String.length line+1<=1024*1024)"unchanged actual frame1MiB";
      check(Yojson.Safe.to_string(Yojson.Safe.from_string line)=line)"canonical native raw line";
      export_bytes:= !export_bytes+String.length prefix+String.length line+1)lines;
    raw_bytes:= !raw_bytes+String.length text;
    name,lines,`Assoc["name",`String name;"lines",`Int(List.length lines);"bytes",`Int(String.length text)])files in
  let ending="V3_CAPTURE_END="^Yojson.Safe.to_string(`Assoc[
    "schema",`Int 1;"captureSchema",`Int 3;"capturePolicy",`String "linked-program-capture-bounded-v3";
    "files",`List(List.map(fun(_,_,meta)->meta)exports);"rawBytes",`Int !raw_bytes;
    "rawLineExportBytes",`Int !export_bytes;"requiresNativeSuccessAndClosedWriter",`Bool true;
    "proofAccepted",`Bool false])^"\n"in
  check(!raw_bytes<=4*1024*1024&& !export_bytes+String.length ending<=4*1024*1024)"bounded complete native export";
  List.iter(fun(name,lines,_)->List.iter(fun line->Printf.printf "V3_CAPTURE_LINE=%s:%s\n"name line)lines)exports;
  Printf.printf "%s%!"ending)
let v3_security () =
  let ignore_visit _ _=() in
  let input value=ignore(K.checked ~version:3 ~guard:(K.guard_ast_v3 ignore_visit)
    ~to_json:(fun _->`Null) ~of_json:(fun _->Ok value)value)in
  rejects(fun()->input(fun x->x));let rec cycle=1::cycle in rejects(fun()->input cycle);
  rejects(fun()->input Int64.max_int);rejects(fun()->input(Array.make 262144 0.));
  rejects(fun()->input(List.init 2049 Fun.id));rejects(fun()->input(String.make 65537 'x'));
  rejects(fun()->input(List.init 5(fun _->String.make 65536 'x')));
  let oversized=crossing_expr 128 256 in
  check(String.starts_with ~prefix:"value nodes/depth budget nodes=131073"
    (incomplete_reason(fun()->K.guard_ast_v3 visit_expr oversized)))"finite V3 typed node ceiling";
  let small=Expr.Lit(Literal.Bool true)in
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3 ~guard:(K.guard_ast_v3 visit_expr)
    ~to_json:Expr.to_yojson ~of_json:(fun _->Ok oversized)small))in
  check(String.ends_with ~suffix:"stage=typed-decoded" why)"decoded typed node guard remains required";
  let bad_z=Literal.Int(Z.shift_left Z.one 65536)and good_z=Literal.Int Z.one in
  rejects(fun()->ignore(C.ast ~version:3(fun v x->v#visit_literal () x)Literal.to_yojson Literal.of_yojson bad_z));
  let why=incomplete_reason(fun()->ignore(C.ast ~version:3(fun v x->v#visit_literal () x)
    Literal.to_yojson(fun _->Ok bad_z)good_z))in
  check(String.ends_with ~suffix:"stage=typed-decoded" why)"decoded Z guard remains required";
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3 ~guard:(K.guard_ast_v3 ignore_visit)
    ~to_json:(fun _->`Null) ~of_json:(fun _->Ok(String.make 65537 'x'))"small"))in
  check(String.ends_with ~suffix:"stage=typed-decoded" why)"decoded string guard remains required"
let v3_typed_depth () =
  (* EList's outer block and Lit/Bool payload add exactly three edges to
     the flat list spine. Each boundary uses real Expr.t and its real visitor. *)
  let value depth = Expr.EList(List.init (depth-3)(fun _->Expr.Lit(Literal.Bool true)))in
  let small=Expr.Lit(Literal.Bool true)in
  List.iter(fun depth->
    let actual=value depth in
    ignore(K.inspect ~node_limit:131072 ~depth_limit:depth actual);
    rejects(fun()->ignore(K.inspect ~node_limit:131072 ~depth_limit:(depth-1) actual));
    K.guard_ast visit_expr actual;
    let encoded=C.ast ~version:2 visit_expr Expr.to_yojson Expr.of_yojson actual in
    check(K.equal(K.untag encoded)(Expr.to_yojson actual))
      (Printf.sprintf "legacy actual typed roundtrip at depth%d" depth)) [511;512];
  let why=incomplete_reason(fun()->ignore(K.inspect(value 513)))in
  check(String.ends_with ~suffix:"depth=513 depth_limit=512 nodes_exceeded=0 depth_exceeded=1" why)
    "legacy inspect default remains512";
  let conversions=ref 0 in
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3
    ~guard:(K.guard_ast visit_expr)
    ~to_json:(fun x->incr conversions;Expr.to_yojson x) ~of_json:Expr.of_yojson(value 513)))in
  check(!conversions=0&&String.ends_with
    ~suffix:"depth=513 depth_limit=512 nodes_exceeded=0 depth_exceeded=1 stage=typed-input" why)
    "legacy AST guard remains512 before conversion";
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3
    ~guard:(K.guard_ast visit_expr) ~to_json:(fun _->`Null)
    ~of_json:(fun _->Ok(value 513)) small))in
  check(String.ends_with
    ~suffix:"depth=513 depth_limit=512 nodes_exceeded=0 depth_exceeded=1 stage=typed-decoded" why)
    "legacy AST decoded guard remains512";
  List.iter(fun depth->
    let actual=value depth in
    ignore(K.inspect ~node_limit:131072 ~depth_limit:depth actual);
    rejects(fun()->ignore(K.inspect ~node_limit:131072 ~depth_limit:(depth-1) actual));
    K.guard_ast_v3 visit_expr actual;
    (* Constant JSON deliberately isolates the two real typed guard stages
       from independent transport depth. This is not a real AST codec fit claim;
       the existing real crossing/roundtrip controls remain unchanged. *)
    let guards=ref 0 and conversions=ref 0 and decodes=ref 0 in
    let encoded=K.checked ~version:3
      ~guard:(fun x->incr guards;K.guard_ast_v3 visit_expr x)
      ~to_json:(fun _->incr conversions;`Null)
      ~of_json:(fun _->incr decodes;Ok actual) actual in
    check(!guards=2&& !conversions=2&& !decodes=1&&K.equal encoded(K.tag `Null))
      (Printf.sprintf "both V3 typed stages accept exact physical depth%d" depth)) [2047;2048];
  let too_deep=value 2049 in
  let conversions=ref 0 and decodes=ref 0 in
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3
    ~guard:(K.guard_ast_v3 visit_expr)
    ~to_json:(fun _->incr conversions;`Null)
    ~of_json:(fun _->incr decodes;Ok too_deep) too_deep))in
  check(!conversions=0&& !decodes=0&&String.ends_with
    ~suffix:"depth=2049 depth_limit=2048 nodes_exceeded=0 depth_exceeded=1 stage=typed-input" why)
    "V3 depth2049 rejects before input conversion";
  let conversions=ref 0 and decodes=ref 0 in
  let why=incomplete_reason(fun()->ignore(K.checked ~version:3
    ~guard:(K.guard_ast_v3 visit_expr)
    ~to_json:(fun _->incr conversions;`Null)
    ~of_json:(fun _->incr decodes;Ok too_deep) small))in
  check(!conversions=1&& !decodes=1&&String.ends_with
    ~suffix:"depth=2049 depth_limit=2048 nodes_exceeded=0 depth_exceeded=1 stage=typed-decoded" why)
    "V3 depth2049 rejects decoded value before reencoding";
  let why=incomplete_reason(fun()->ignore(C.ast ~version:3 visit_expr
    Expr.to_yojson (fun _->Ok(Expr.Lit(Literal.Bool false))) small))in
  check(why="typed roundtrip mismatch")"V3 real typed roundtrip mismatch still rejects"
let v3_transport_limits () =
  let wide rows columns=`List(List.init rows(fun _->`List(List.init columns(fun _->`Int 0))))in
  let reason json=incomplete_reason(fun()->ignore(K.checked ~version:3 ~to_json:(fun _->json)~of_json:(fun _->Ok 0)0))in
  check(String.ends_with ~suffix:"stage=derived-json"(reason(wide 512 512)))"finite V3 derived occurrences";
  check(String.ends_with ~suffix:"stage=tagged-payload"(reason(wide 128 1024)))"finite V3 tagged occurrences";
  rejects(fun()->K.guard_transport_v3(Array.make 8388608 0.));
  rejects(fun()->K.guard_transport_v3(List.init 2049 Fun.id));
  rejects(fun()->K.guard_transport_v3(String.make 524289 'x'));
  rejects(fun()->K.guard_transport_v3(List.init 3(fun _->String.make 524288 'x')));
  check(reason(`List(List.init 17(fun _->`String(String.make 65536 'x'))))=
    "value string budget stage=derived-json")"unchanged aggregate string bound";
  check(reason(`String(String.make 262145 'x'))="raw string budget")"unchanged raw hex bound";
  check(reason(`List(List.init 128(fun _->`String(String.make 4090 'x'))))=
    "encoded fragment1MiB cap")"unchanged encoded fragment bound";
  rejects(fun()->fresh(fun root->ignore(W.create ~limit:67108865L root)));
  with_writer(fun _ w->W.start w 0;rejects(fun()->W.write w(String.make(1024*1024+1)'x')));
  with_writer ~limit:262144L(fun _ w->W.start w 0;rejects(fun()->W.write w(String.make 200000 'x')))
let v3_negotiation () =
  check(C.version_of_policy None=1&&C.version_of_policy(Some "linked-program-capture-v1")=1)"V1 default unchanged";
  check(C.version_of_policy(Some "linked-program-capture-single-frame-v2")=2)"V2 explicit unchanged";
  check(C.version_of_policy(Some "linked-program-capture-bounded-v3")=3)"V3 explicit only";
  List.iter(fun p->rejects(fun()->ignore(C.version_of_policy(Some p))))
    ["";"3";"linked-program-capture-typed-input-v3";"linked-program-capture-bounded-v3 "];
  rejects(fun()->ignore(K.checked ~version:4 ~to_json:C.jint ~of_json:C.int_of_json 0));
  let prog,_=fixture()in let frames=ref[]in
  C.iter_program ~version:3 ~annot_to_json:Annot.Basic.to_yojson ~annot_of_json:Annot.Basic.of_yojson
    ~phase:"linked"~emit:(fun f->frames:=f:: !frames)prog;
  let frames=List.rev !frames in C.validate_frames ~version:3 frames;
  List.iter(fun version->rejects(fun()->C.validate_frames ~version frames))[1;2;4];
  rejects(fun()->C.validate_frames ~version:3(List.tl frames))
let scope_fixture () =
  let target = Expr.EList [Expr.Lit (Literal.Loc "$lg"); Expr.LVar "#activation"] in
  let binding = Spec.{vsb_source=Expr.PVar "x__scope_f";vsb_target=target} in
  let case = Spec.s_init ~ss_verifier_scope:binding ([Asrt.Emp],None)
      [([Asrt.pred "Activation" [target] []],None)] None Flag.Normal true in
  Spec.init "scopefn" [] [case] false false true None,case
let scope_roundtrip () =
  let spec,case=scope_fixture() in
  Spec.validate_verifier_scope case;
  ignore(K.checked ~guard:(K.guard_ast(fun v x->v#visit_spec () x))
    ~to_json:Spec.to_yojson ~of_json:Spec.of_yojson spec);
  let module Parser=Gillian.Gil_parsing.Make(Annot.Basic) in
  let text=Format.asprintf "%a\nproc scopefn() { ret := undefined; return };" Spec.pp spec in
  let parsed=match Parser.parse_eprog_from_string text with
    | Ok p->Option.get (Prog.get_proc_exn p.labeled_prog "scopefn").proc_spec
    | Error _->Alcotest.fail "GIL metadata text parse" in
  let restored=List.hd parsed.spec_sspecs in
  check(restored.ss_verifier_scope=case.ss_verifier_scope)"GIL text metadata roundtrip";
  check(List.map fst restored.ss_posts=List.map fst case.ss_posts)"public posts roundtrip";
  let prog,proc=fixture() in
  let proc={proc with proc_name="scopefn";proc_spec=Some spec} in
  Hashtbl.replace prog.procs "scopefn" proc;
  let frames=collect "linked" prog in C.validate_frames frames;
  let expected=Spec.to_yojson spec in
  check(List.exists(fun(f:C.frame)->f.kind="proc-field" &&
    (match f.route with ["procs";_;"scopefn";_;"proc_spec"]->true|_->false) && K.equal(K.untag f.payload)expected)frames)
    "linked capture retains verifier metadata"
let scope_defaults_and_rejections () =
  let spec,case=scope_fixture() in
  let absent={case with ss_verifier_scope=None} in
  let legacy=Spec.{spec with spec_sspecs=[absent]} in
  let wire=Spec.to_yojson legacy in
  let rec without_field=function
    | `Assoc fields->`Assoc(List.filter_map(fun(k,v)->
        if k="ss_verifier_scope" then None else Some(k,without_field v))fields)
    | `List xs->`List(List.map without_field xs)|x->x in
  (match Spec.of_yojson(without_field wire)with
   | Ok s->check((List.hd s.spec_sspecs).ss_verifier_scope=None)"legacy JSON default"
   | Error _->Alcotest.fail "missing JSON option must default None");
  (match Spec.of_yojson wire with
   | Ok s->check((List.hd s.spec_sspecs).ss_verifier_scope=None)"valid None JSON representation"
   | Error _->Alcotest.fail "valid None JSON must decode");
  let b=Option.get case.ss_verifier_scope in
  let some_wire=Spec.to_yojson spec in
  let rewrite_metadata value =
    let replacements=ref 0 in
    let rec rewrite=function
      | `Assoc fields->`Assoc(List.map(fun(k,v)->
          if k="ss_verifier_scope"then (incr replacements;k,value)
          else k,rewrite v)fields)
      | `List xs->`List(List.map rewrite xs)|x->x in
    let changed=rewrite some_wire in
    Alcotest.(check int) "exactly one present metadata rewrite" 1 !replacements;
    check(not(K.equal changed some_wire))"metadata control changes the Some wire";
    changed in
  List.iter(fun(label,value)->
    check(Result.is_error(Spec.of_yojson(rewrite_metadata value)))
      ("present malformed metadata rejected: "^label))[
    "String",`String "malformed";
    "scalar",`Int 0;
    "incomplete binding",`Assoc["vsb_source",Expr.to_yojson b.vsb_source]];
  (match Spec.of_yojson(rewrite_metadata `Null)with
   | Ok s->check((List.hd s.spec_sspecs).ss_verifier_scope=None)"explicit null remains valid None"
   | Error _->Alcotest.fail "option null must remain None");
  List.iter(fun bad->rejects(fun()->Spec.validate_verifier_scope bad))[
    {case with ss_flag=Flag.Error};{case with ss_to_verify=false};
    {case with ss_verifier_scope=Some{b with vsb_source=Expr.LVar "#ghost"}};
    {case with ss_verifier_scope=Some{b with vsb_target=Expr.LVar "#activation"}};
    {case with ss_verifier_scope=Some{b with vsb_target=Expr.EList[Expr.LVar "#orphan"]}};
    {case with ss_pre=([Asrt.Pure(Expr.BinOp(Expr.LVar "#activation",Equal,Expr.LVar "#activation"))],None)}];
  let detached={case with ss_verifier_scope=Some{b with
    vsb_target=Expr.EList[Expr.Lit Literal.Null;Expr.LVar "#activation"]}} in
  rejects(fun()->Spec.validate_verifier_scope ~exact_target:true detached);
  check(Spec.hash_of_t spec<>Spec.hash_of_t legacy)"metadata changes spec hash";
  let changed={case with ss_verifier_scope=Some{b with vsb_source=Expr.PVar "missing"}} in
  check(Spec.hash_of_t spec<>Spec.hash_of_t{spec with spec_sspecs=[changed]})"source changes identity";
  check(Result.is_error(Spec.require_verifier_scope_source changed.ss_verifier_scope ~mem:(fun _->false)))
    "missing final binding is explicit failure";
  check(Result.is_ok(Spec.require_verifier_scope_source case.ss_verifier_scope
    ~mem:(fun name->List.mem_assoc name ["x__scope_f",Expr.Lit Literal.Undefined])))
    "defined undefined is present, never an assumed scope"
let scope_alpha_and_private_posts () =
  let spec,case=scope_fixture() in
  let rename=object inherit [_] Visitors.endo as super
    method! visit_expr () e=match e with
      |Expr.LVar "#activation"->Expr.LVar "#renamed"
      |Expr.PVar "x__scope_f"->Expr.PVar "renamed_source"
      |_->super#visit_expr () e end in
  let renamed=rename#visit_spec () spec in
  let case'=List.hd renamed.spec_sspecs in Spec.validate_verifier_scope case';
  let b=Option.get case'.ss_verifier_scope in
  check(Expr.equal b.vsb_source(Expr.PVar "renamed_source"))"source alpha transport";
  check(Utils.Containers.SS.mem "#renamed"(Asrt.lvars(fst(List.hd case'.ss_posts))))
    "public witness alpha transport";
  let subst=Gillian.Symbolic.Subst.init [Expr.LVar "#activation",Expr.LVar "#normalised"] in
  let partial=Gillian.Symbolic.Subst.subst_in_expr subst ~partial:true in
  let normalized={case with
    ss_posts=List.map(fun(a,l)->Gillian.Symbolic.Subst.substitute_asrt subst ~partial:true a,l)case.ss_posts;
    ss_verifier_scope=Option.map(Spec.map_verifier_scope partial)case.ss_verifier_scope} in
  Spec.validate_verifier_scope normalized;
  check(List.length(fst(List.hd(Spec.verifier_posts normalized)))=2)"private equality added only for verification";
  check(List.length(fst(List.hd normalized.ss_posts))=1)"saved public posts unchanged";
  (* The public program initializer runs the real internal init_specs path;
     the fixture has no unrelated predicates/lemmas or trusted declarations. *)
  let _,proc=fixture() in
  let empty ()=Hashtbl.create 1 in
  let procs=empty() in
  Hashtbl.add procs "scopefn"
    {proc with proc_name="scopefn";proc_params=[];proc_spec=Some spec};
  let program=Prog.make ~imports:[] ~lemmas:(empty()) ~preds:(empty())
    ~funcs:(empty()) ~datatypes:(empty()) ~only_specs:(empty()) ~procs
    ~macros:(empty()) ~bi_specs:(empty()) ~proc_names:["scopefn"]
    ~predecessors:(empty()) () in
  let caller=Engine.MP.init_prog program in
  let saved=Hashtbl.find caller.specs "scopefn" in
  check(saved.data=spec)"saved AST retains identity metadata";
  let rec leaves=function
    |Engine.MP.Choice(a,b)->leaves a @ leaves b
    |Engine.MP.ConsumeStep(_,tail)|Engine.MP.LabelStep(_,tail)->leaves tail
    |Engine.MP.Finished(Some(_,posts))->posts
    |Engine.MP.Finished None->[] in
  let posts=leaves saved.mp in
  check(posts=List.map fst case.ss_posts)"caller Finished posts are public only";
  check(List.for_all(fun p->not(Utils.Containers.SS.mem "x__scope_f"(Asrt.pvars p)))posts)
    "compiler local does not leak into caller semantic posts"

(* V4 tests exercise the real fragment writer/inverse, not a parallel codec. *)
let v4_rejects f = ignore(incomplete_reason f)
module F4 = C.Fragments
let v4_parts write value =
  let parts=ref [] in
  write ~emit:(fun kind route payload->parts:=(kind,route,payload):: !parts)
    ~route:["fixture"] value;
  List.rev !parts
let v4_restore read parts =
  let rest=ref parts in
  let take kind route=match !rest with
    | (k,r,payload)::tail ->
        check(k=kind && r=route)"exact fragment route/order";
        rest:=tail;K.guard_transport_v3 payload;K.untag payload
    | [] -> raise(K.Incomplete "missing fixture fragment") in
  let value=read ~take ~route:["fixture"] in
  check(!rest=[])"no extra fragments";value
let v4_collect phase prog =
  let out=ref [] in C.iter_program ~version:4
    ~annot_to_json:Annot.Basic.to_yojson ~annot_of_json:Annot.Basic.of_yojson
    ~phase ~emit:(fun f->out:=f:: !out)prog;
  List.rev !out
let v4_contains text part =
  let rec loop i =
    i+String.length part<=String.length text &&
    (String.sub text i (String.length part)=part || loop(i+1)) in loop 0
let v4_fields () =
  let prog,proc=fixture() in
  let pred=Hashtbl.find prog.preds "P" in
  let values=[Expr.PVar "x";Expr.LVar "#x";Expr.ALoc "#a";Expr.Lit(Literal.Loc "$l");
    Expr.Lit(Literal.Num(-0.));Expr.Lit(Literal.Num(Int64.float_of_bits 0x7ff8000000000011L));
    Expr.Lit(Literal.Int(Z.shift_left Z.one 100));
    Expr.Lit(Literal.String "\000\255");
    Expr.Lit(Literal.Utf16String(Utf16.of_canonical(Utf16.of_code_units[0;0xd800;0xdfff])))] in
  let atoms=[Asrt.Emp;Asrt.Pure(List.hd values);
    Asrt.Types[List.hd values,Type.ObjectType;Expr.LVar "#x",Type.Utf16Type];
    Asrt.CorePred("raw\000\255",values,List.rev values);
    Asrt.Wand{lhs=("left",values);rhs=("right",List.rev values)}] in
  let pred={pred with pred_name="raw\000\255";pred_source_path=Some "";pred_internal=true;
    pred_num_params=(-7);ins_number=99;pred_params=["x",None;"x",Some Type.ObjectType];
    pred_definitions=[None,[];Some("",[]),[Asrt.Emp];Some("D",["e";"e"]),atoms];
    pred_facts=values;pred_guard=Some[];pred_pure=true;pred_abstract=true;
    pred_nounfold=true;pred_normalised=true} in
  let got=v4_restore F4.take_pred(v4_parts F4.emit_pred pred) in
  check(K.equal(F4.pred_to_yojson pred)(F4.pred_to_yojson got))"all14 predicate fields and atom identity";
  check(got.pred_num_params=(-7)&&got.ins_number=99)"scalar counts never normalized";
  List.iter(fun guard->
    let p={pred with pred_guard=guard} in
    check(K.equal(F4.pred_to_yojson p)(F4.pred_to_yojson(v4_restore F4.take_pred(v4_parts F4.emit_pred p))))
      "None/Some-empty/Some-Emp guard")[None;Some[];Some[Asrt.Emp]];
  let scope,_=scope_fixture() in
  let case=List.hd scope.spec_sspecs in
  let original_case=List.hd(Option.get proc.proc_spec).spec_sspecs in
  let location=snd original_case.ss_pre in
  let case={case with ss_pre=(atoms,location);
    ss_posts=[([],None);([Asrt.Emp],location);(atoms,None)];
    ss_variant=Some(Expr.LVar "#variant");ss_flag=Flag.Bug;ss_to_verify=false;
    ss_label=Some("",["e";"e"])} in
  let spec=Spec.{spec_name="s\000\255";spec_params=["x";"x"];
    spec_sspecs=[case;{case with ss_verifier_scope=None;ss_variant=None;ss_label=None};
      {case with ss_label=Some("",[])}];spec_normalised=true;spec_incomplete=true;
    spec_to_verify=false;spec_location=location} in
  let got=v4_restore F4.take_spec(v4_parts F4.emit_spec spec) in
  check(K.equal(Spec.to_yojson spec)(Spec.to_yojson got))"all7 spec and7 singleSpec fields";
  List.iter(fun value->
    check(K.equal
      (Spec.to_yojson(match value with Some s->s|None->spec))
      (Spec.to_yojson(match v4_restore F4.take_optional_spec(v4_parts F4.emit_optional_spec value)with
       Some s->s|None->spec)))"optional spec exact fields";
    check((value=None)=(v4_restore F4.take_optional_spec(v4_parts F4.emit_optional_spec value)=None))
      "None versus Some empty spec") [None;Some spec;Some{spec with spec_sspecs=[]}];
  (* A self-consistent value replacement is not a grammar error. Compare the
     reconstructed source/target association to its expected original instead. *)
  let parts=v4_parts F4.emit_spec spec in
  let source=["fixture";"spec_sspecs";"0";"ss_verifier_scope";"some";"vsb_source"]
  and target=["fixture";"spec_sspecs";"0";"ss_verifier_scope";"some";"vsb_target"] in
  let payload route=let _,_,p=List.find(fun(_,r,_)->r=route)parts in p in
  let changed=List.map(fun(k,r,p)->k,r,(if r=source then payload target else if r=target then payload source else p))parts in
  let digest parts=Digest.string(Yojson.Safe.to_string(`List(List.map(fun(k,r,p)->
    `List[`String k;`List(List.map(fun s->`String s)r);p])parts)))in
  check(digest parts<>digest changed)"metadata mutant owns different wire fingerprint";
  let got=v4_restore F4.take_spec changed in
  check(not(K.equal(Spec.to_yojson spec)(Spec.to_yojson got)))
    "swapped metadata fails expected-original identity, not grammar inference"
let v4_flat_and_depth () =
  let prog,_=fixture() in let base=Hashtbl.find prog.preds "P" in
  let p={base with pred_definitions=[None,List.init 2055(fun _->Asrt.Emp)];
    pred_params=List.init 2055(fun i->string_of_int i,None);
    pred_facts=List.init 2055(fun _->Expr.Lit(Literal.Bool true));
    pred_guard=Some[]} in
  v4_rejects(fun()->K.guard_ast_v3(fun v x->v#visit_pred () x)p);
  let got=v4_restore F4.take_pred(v4_parts F4.emit_pred p) in
  check(K.equal(F4.pred_to_yojson p)(F4.pred_to_yojson got))"long flat containers exact typed reconstruction without whole JSON";
  let spec,_=scope_fixture() in let s=List.hd spec.spec_sspecs in
  let spec={spec with spec_params=List.init 2055 string_of_int;spec_sspecs=[
    {s with ss_pre=(List.init 2055(fun _->Asrt.Emp),None);
      ss_label=Some("L",List.init 2055 string_of_int)}]} in
  v4_rejects(fun()->K.guard_ast_v3(fun v x->v#visit_spec () x)spec);
  check(K.equal(Spec.to_yojson spec)(Spec.to_yojson(v4_restore F4.take_spec(v4_parts F4.emit_spec spec))))
    "long spec PRE/params/label containers exact";
  let rec deep n e=if n=0 then e else deep(n-1)(Expr.UnOp(Not,e))in
  let bad={base with pred_facts=[deep 2050(Expr.Lit(Literal.Bool true))]} in
  let why=incomplete_reason(fun()->ignore(v4_parts F4.emit_pred bad))in
  check(v4_contains why "depth=2049" && v4_contains why (K.hex "pred_facts"))
    "over-depth Expr rejects with exact facts route, no fallback"
let v4_aggregate () =
  ignore(K.inspect_parent_v4(Array.make 131071 0));
  check(incomplete_reason(fun()->ignore(K.inspect_parent_v4(Array.make 131072 0)))=
    "V4 parent node budget")"exact parent131072 occurrences and one-over";
  ignore(K.inspect_parent_v4(Array.make 262143 0.));
  check(incomplete_reason(fun()->ignore(K.inspect_parent_v4(Array.make 262144 0.)))=
    "V4 parent word budget")"exact parent262144 words and one-over";
  ignore(K.inspect_parent_v4(String.make 65536 'x'));
  v4_rejects(fun()->ignore(K.inspect_parent_v4(String.make 65537 'x')));
  let shared=String.make 65536 'x' in
  ignore(K.inspect_parent_v4[shared;shared;shared;shared]);
  v4_rejects(fun()->ignore(K.inspect_parent_v4[shared;shared;shared;shared;shared]));
  let rec cycle=0::cycle in v4_rejects(fun()->ignore(K.inspect_parent_v4 cycle));
  v4_rejects(fun()->ignore(K.inspect_parent_v4(fun x->x)));
  v4_rejects(fun()->K.check_parent_customs_v4(K.inspect_parent_v4 Int64.max_int)[]);
  let prog,_=fixture()in let p=Hashtbl.find prog.preds "P"in
  let z bits={p with pred_facts=[Expr.Lit(Literal.Int(Z.shift_left Z.one(bits-1)))]}in
  ignore(v4_parts F4.emit_pred(z 65536));
  v4_rejects(fun()->ignore(v4_parts F4.emit_pred(z 65537)))
let v4_grammar () =
  let prog,proc=fixture()in let spec,_=scope_fixture()in
  Hashtbl.replace prog.procs "p" {proc with proc_spec=Some spec};
  Hashtbl.replace prog.only_specs "p" spec;
  let pred=Hashtbl.find prog.preds "P"in
  Hashtbl.add prog.preds "P" {pred with pred_internal=true};
  Hashtbl.add prog.predecessors ("p",2,1)7;
  let frames=v4_collect "linked" prog in C.validate_frames ~version:4 frames;
  let renumber=List.mapi(fun seq(f:C.frame)->{f with seq})in
  let wire frames=List.map(fun f->C.frame_of_json ~version:4
    (Yojson.Safe.from_string(Yojson.Safe.to_string(C.frame_json ~version:4 f))))frames in
  let hash frames=Digest.string(String.concat "\n"
    (List.map(fun f->Yojson.Safe.to_string(C.frame_json ~version:4 f))frames))in
  let reject_mutant changed =
    check(hash frames<>hash changed)"own fingerprint changes before real grammar";
    v4_rejects(fun()->C.validate_frames ~version:4(wire changed))in
  let route=["preds";"0";"P";"0";"pred_name"]in
  let index=fst(List.find(fun(_,(f:C.frame))->f.route=route)(List.mapi(fun i f->i,f)frames))in
  let arr=Array.of_list frames in
  reject_mutant(renumber(List.filter(fun(f:C.frame)->f.route<>route)frames));
  reject_mutant(renumber(List.concat_map(fun(f:C.frame)->if f.route=route then[f;f]else[f])frames));
  let swap=Array.copy arr in let tmp=swap.(index)in
  swap.(index)<-swap.(index+1);swap.(index+1)<-tmp;
  reject_mutant(renumber(Array.to_list swap));
  reject_mutant(List.map(fun(f:C.frame)->if f.route=route then{f with phase="post-logic"}else f)frames);
  reject_mutant(List.map(fun(f:C.frame)->if f.route=route then{f with route=["preds";"0";"P";"1";"pred_name"]}else f)frames);
  reject_mutant(List.map(fun(f:C.frame)->
    if f.route=["preds";"0";"P";"0";"pred_definitions"]then{f with payload=K.tag(`Int 2)}else f)frames);
  reject_mutant(List.map(fun(f:C.frame)->
    if f.kind="fragment-close"&&f.route=["preds";"0";"P";"0"]then{f with kind="fragment-open"}else f)frames);
  reject_mutant(List.map(fun(f:C.frame)->
    if f.route=["only_specs";"0";"p";"0";"spec_sspecs";"0";"ss_verifier_scope";"some";"vsb_source"]
    then{f with route=["only_specs";"0";"p";"0";"spec_sspecs";"0";"ss_verifier_scope";"some";"vsb_target"]}else f)frames);
  reject_mutant(renumber(List.tl(List.rev frames)|>List.rev));
  reject_mutant(renumber(frames@[List.hd frames]));
  let flags=List.filter_map(fun(f:C.frame)->match f.route with
    |["preds";"0";"P";_;"pred_internal"]->Some(K.untag f.payload)|_->None)frames in
  check(flags=[`Bool true;`Bool false])"V4 duplicate bindings remain latest-first";
  List.iter(fun table->check(List.exists(fun(f:C.frame)->f.kind="table"&&f.route=[table])frames)
    ("mandatory V4 table "^table))C.tables
let v4_policy_and_phases () =
  check(C.version_of_policy(Some"linked-program-capture-fragmented-v4")=4)"explicit schema4 only";
  List.iter(fun name->v4_rejects(fun()->ignore(C.version_of_policy(Some name))))
    ["linked-program-capture-fragmented-v4 ";"4";"linked-program-capture-v4"];
  let prog,_=fixture()in
  let frames=v4_collect "post-logic" prog in C.validate_frames ~version:4 frames;
  List.iter(fun version->v4_rejects(fun()->C.validate_frames ~version frames))[1;2;3];
  with_writer(fun root writer->
    let session:C.session={writer;version=4;next=0;counts=[]}in
    List.iter(fun phase->C.capture(Some session)~annot_to_json:Annot.Basic.to_yojson
      ~annot_of_json:Annot.Basic.of_yojson ~phase prog)["linked";"post-logic"];
    let f=open_in_bin(Filename.concat root"00000002.jsonl")in
    let raw=Fun.protect ~finally:(fun()->close_in f)(fun()->really_input_string f(in_channel_length f))in
    let expected=`Assoc["schema",`Int 4;"codecPolicy",`String"linked-program-capture-fragmented-v4";
      "phaseFiles",`List[`String"00000000.jsonl";`String"00000001.jsonl"];
      "frameCounts",`List(List.map(fun n->`Int n)session.counts);
      "requiresNativeSuccessAndClosedWriter",`Bool true;"proofAccepted",`Bool false]in
    check(K.equal(Yojson.Safe.from_string raw)expected)"V4 closed manifest exact";
    let failure,sealed,dir,active,_,_,phases,uncertain=W.snapshot writer in
    check(failure=None&&sealed&&dir&&active&&phases=3&&not uncertain)"unchanged Writer custody")

(* Batching tests use only the public capture/session and Writer IO APIs. *)
let batch_capture session phase prog =
  C.capture(Some session) ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase prog
let batch_lines version phase prog =
  let lines=ref [] in
  C.iter_program ~version ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase
    ~emit:(fun frame->lines:=(Yojson.Safe.to_string(C.frame_json ~version frame)^"\n"):: !lines)prog;
  List.rev !lines
let batch_read root name =
  let input=open_in_bin(Filename.concat root name) in
  Fun.protect ~finally:(fun()->close_in input)(fun()->
    let n=in_channel_length input in
    check(n>0&&n<=4*1024*1024)"bounded batch fixture file";
    really_input_string input n)
let batch_large_fixture () =
  let prog,proc=fixture() in
  let anno,_,_=proc.proc_body.(0) in
  let command=Cmd.Assignment("x",Expr.Lit(Literal.String(String.make 65536 'x'))) in
  Hashtbl.replace prog.procs "p" {proc with
    proc_body=Array.init 9(fun i->anno,Some i,command)};
  prog
let batch_observer () =
  let names=Hashtbl.create 4 and writes=ref [] and events=ref [] in
  let name fd=Hashtbl.find_opt names fd in
  let io={W.system_io with
    create_at=(fun dir file->let fd=W.system_io.create_at dir file in
      Hashtbl.replace names fd file;fd);
    write=(fun fd bytes at n->
      if at=0 then (
        let file=Option.get(name fd) in
        let text=Bytes.sub_string bytes 0 n in
        writes:=(file,text):: !writes;events:=("write",file):: !events);
      Unix.write fd bytes at n);
    fsync=(fun fd->Unix.fsync fd;
      Option.iter(fun file->events:=("fsync",file):: !events)(name fd));
    close=(fun fd->let file=name fd in Unix.close fd;
      Option.iter(fun file->Hashtbl.remove names fd;events:=("close",file):: !events)file)} in
  io,writes,events
let batch_identity_and_closure () =
  let prog=batch_large_fixture() in
  let io,writes,events=batch_observer() in
  with_writer ~io(fun root writer->
    let session:C.session={writer;version=4;next=0;counts=[]} in
    List.iteri(fun index phase->
      let expected=batch_lines 4 phase prog in
      let text=String.concat "" expected in
      check(String.length text>K.fragment_bytes&&String.length text<=2*K.fragment_bytes)
        "bounded fixture crosses one batch without giant input";
      List.iter(fun line->check(String.length line<=K.fragment_bytes)
        "individual complete frame including LF capped")expected;
      batch_capture session phase prog;
      let file=Printf.sprintf "%08d.jsonl" index in
      let chunks=List.rev !writes |> List.filter_map(fun(name,text)->if name=file then Some text else None) in
      check(List.length chunks>=2&&List.length chunks<List.length expected)
        "overflow creates multiple whole-frame batches";
      Alcotest.(check string) "original emitted JSONL byte identity" text(batch_read root file);
      Alcotest.(check string) "all captured write chunks identical" text(String.concat "" chunks);
      List.iter(fun chunk->
        check(String.length chunk>0&&String.length chunk<=K.fragment_bytes)
          "each Writer.write chunk bounded";
        check(String.ends_with ~suffix:"\n" chunk)"chunk ends at whole-frame LF";
        let lines=String.sub chunk 0(String.length chunk-1)|>String.split_on_char '\n' in
        List.iter(fun line->ignore(C.frame_of_json ~version:4(Yojson.Safe.from_string line)))lines)chunks;
      let actual=List.filter(fun(_,name)->name=file)(List.rev !events) in
      let expected_events=List.concat_map(fun _->["write",file;"fsync",file])chunks @
        ["fsync",file;"close",file] in
      check(actual=expected_events)"each batch fsynced and final phase flushed before close";
      check(session.next=index+1&&List.nth session.counts index=List.length expected)
        "phase advances only after flush/close with unchanged frame count") ["linked";"post-logic"];
    let expected=`Assoc["schema",`Int 4;"codecPolicy",`String"linked-program-capture-fragmented-v4";
      "phaseFiles",`List[`String"00000000.jsonl";`String"00000001.jsonl"];
      "frameCounts",`List(List.map(fun n->`Int n)session.counts);
      "requiresNativeSuccessAndClosedWriter",`Bool true;"proofAccepted",`Bool false] in
    Alcotest.(check string)"unchanged manifest bytes"(Yojson.Safe.to_string expected^"\n")
      (batch_read root "00000002.jsonl");
    let failure,sealed,dir,active,intended,written,phases,uncertain=W.snapshot writer in
    let size=List.fold_left(fun n file->n+String.length(batch_read root file))0
      ["00000000.jsonl";"00000001.jsonl";"00000002.jsonl"] in
    check(failure=None&&sealed&&dir&&active&&phases=3&&not uncertain)
      "complete writer retains closed certainty";
    check(intended=Int64.of_int size&&written=intended)"all bytes charged once without counter reset")
let batch_error injected =
  Gillian_result.Exc.Gillian_error(Gillian_result.Error.OperationError
    ("Linked program capture incomplete: "^Printexc.to_string injected))
let batch_failed_state root writer session =
  check(session.C.next=0&&session.counts=[])"failed phase never committed";
  check(not(Sys.file_exists(Filename.concat root"00000001.jsonl"))&&
    not(Sys.file_exists(Filename.concat root"00000002.jsonl")))"no second phase or false manifest";
  let failure,_,_,_,intended,written,phases,_=W.snapshot writer in
  check(failure<>None&&phases=0&&intended>0L&&written<=intended)
    "Writer failure and prospective byte accounting remain latched"
let batch_failure mode () =
  let injected=K.Incomplete("injected V4 batch "^mode) in
  let attempts=ref 0 in
  let io=match mode with
    |"phase-write"|"overflow-write"->{W.system_io with write=(fun _ _ _ _->
        incr attempts;raise injected)}
    |"fsync"->{W.system_io with fsync=(fun fd->
        if (Unix.fstat fd).Unix.st_kind=Unix.S_REG then (incr attempts;raise injected)
        else Unix.fsync fd)}
    |"close"->{W.system_io with close=(fun fd->
        let regular=(Unix.fstat fd).Unix.st_kind=Unix.S_REG in
        Unix.close fd;if regular then (incr attempts;raise injected))}
    |_->Alcotest.fail "unknown batch fault" in
  let prog=if mode="overflow-write" then batch_large_fixture() else fst(fixture()) in
  with_writer ~io(fun root writer->
    let session:C.session={writer;version=4;next=0;counts=[]} in
    let expected=if mode="overflow-write" then
      K.Incomplete("injected V4 batch "^mode^
        " phase=linked table=procs keyIndex=0 keyHexPrefix=70 bindingOrdinal=0")
      else injected in
    Alcotest.check_raises "exact injected capture failure, no swallowed write"(batch_error expected)
      (fun()->batch_capture session "linked" prog);
    check(!attempts=1)"failed write/fsync/close is never retried";
    batch_failed_state root writer session;
    if mode="phase-write"||mode="overflow-write" then (
      let _,_,_,_,intended,written,_,_=W.snapshot writer in
      check(intended>0L&&written=0L)"intended survives failed write without invented bytes");
    if mode="close" then (
      let _,_,dir,active,_,_,_,uncertain=W.snapshot writer in
      check(uncertain&&not dir&&not active)"close uncertainty is preserved");
    Alcotest.check_raises "failed phase cannot authorize post-logic or manifest"
      (batch_error(K.Incomplete"snapshot invocation order"))
      (fun()->batch_capture session "post-logic" prog);
    check(!attempts=1)"no later IO after failed phase")
let batch_individual_frame_cap () =
  let prog,_=fixture() in
  let pred=Hashtbl.find prog.preds "P" in
  let key=String.make 65536 'k' in
  Hashtbl.clear prog.preds;
  Hashtbl.add prog.preds key {pred with pred_facts=[crossing_expr 48 256]};
  let frames=v4_collect "linked" prog in
  let oversized=List.filter(fun(frame:C.frame)->
    String.length(Yojson.Safe.to_string(C.frame_json ~version:4 frame))+1>K.fragment_bytes)frames in
  check(oversized<>[])"complete envelope plus LF exceeds cap despite bounded payload";
  List.iter(fun(frame:C.frame)->
    check(String.length(Yojson.Safe.to_string frame.payload)<=K.fragment_bytes)
      "oversized envelope has individually admitted payload")oversized;
  with_writer(fun root writer->
    let session:C.session={writer;version=4;next=0;counts=[]} in
    let expected=K.Incomplete("capture frame1MiB cap fragmentRoute="^
      String.concat "/"(List.map K.hex["pred_facts";"0"])^
      " fragmentRoute="^String.concat "/"(List.map K.hex["preds";"0";key;"0"])^
      " phase=linked table=preds keyIndex=0 keyHexPrefix="^K.hex(String.sub key 0 32)^
      " bindingOrdinal=0") in
    Alcotest.check_raises "V4 complete frame including LF rejected before buffering"
      (batch_error expected)
      (fun()->batch_capture session "linked" prog);
    check(session.next=0&&session.counts=[])"oversize frame cannot commit phase";
    check(not(Sys.file_exists(Filename.concat root"00000002.jsonl")))
      "oversize frame cannot produce manifest")
let batch_legacy_io () =
  let prog,_=fixture() in
  List.iter(fun version->
    let io,writes,_=batch_observer() in
    with_writer ~io(fun _ writer->
      let session:C.session={writer;version;next=0;counts=[]} in
      List.iteri(fun index phase->
        let expected=batch_lines version phase prog in
        batch_capture session phase prog;
        let file=Printf.sprintf "%08d.jsonl" index in
        let actual=List.rev !writes|>List.filter_map(fun(name,text)->if name=file then Some text else None) in
        check(actual=expected)"legacy writes retain one unchanged JSONL frame per write")
        ["linked";"post-logic"])) [1;2;3]

(* V5 tests cover only the new transport through public capture/codec APIs. *)
let v5_policy="linked-program-capture-compact-routes-v5"
let v5_collect phase prog =
  let frames=ref [] in
  C.iter_program ~version:5 ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase ~emit:(fun f->frames:=f:: !frames)prog;
  List.rev !frames
let v5_wire phase frames =
  let encoder=C.V5_route.encoder ~phase in List.map(C.V5_route.encode encoder)frames
let v5_decode phase wire =
  let decoder=C.V5_route.decoder ~phase in List.map(C.V5_route.decode decoder)wire
let v5_same expected actual =
  check(List.length expected=List.length actual)"same complete logical inventory";
  List.iter2(fun(a:C.frame)(b:C.frame)->
    check(a.phase=b.phase&&a.seq=b.seq&&a.kind=b.kind&&a.route=b.route&&K.equal a.payload b.payload)
      "exact six logical fields and raw payload")expected actual
let v5_expect why f = Alcotest.(check string)"exact Codec.Incomplete" why(incomplete_reason f)
let v5_frame seq route = {C.phase="linked";seq;kind="boundary";route;payload=K.tag(`Int seq)}
let v5_pack phase seq kind route payload=`List[`Int 5;`String phase;`Int seq;`String kind;route;payload]
let v5_code = function `List[_;_;_;_;code;_]->code|_->Alcotest.fail "six-field V5 tuple"
let v5_absolute (frame:C.frame) =
  v5_pack frame.phase frame.seq frame.kind (`List(List.map(fun s->`String(K.hex s))frame.route))frame.payload
let v5_capture session phase prog =
  C.capture(Some session) ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase prog
let v5_roundtrip () =
  let prog,proc=fixture() in let spec,case=scope_fixture() in
  Hashtbl.replace prog.procs "p" {proc with proc_spec=Some spec};
  Hashtbl.replace prog.only_specs "p" spec;
  let pred=Hashtbl.find prog.preds "P" in
  Hashtbl.clear prog.preds;
  List.iter(fun key->Hashtbl.add prog.preds key pred)["";"\000\255";"P"];
  Hashtbl.add prog.preds "P" {pred with pred_internal=true};
  Hashtbl.add prog.predecessors("p",2,1)7;
  List.iter(fun phase->
    let frames=v5_collect phase prog in
    let decoded=v5_decode phase(v5_wire phase frames) in
    v5_same frames decoded;C.validate_frames ~version:5 decoded;
    let old=ref [] in C.iter_program ~version:4 ~annot_to_json:Annot.Basic.to_yojson
      ~annot_of_json:Annot.Basic.of_yojson ~phase ~emit:(fun f->old:=f:: !old)prog;
    List.iter2(fun(a:C.frame)(b:C.frame)->
      if a.kind="header" then (
        check(K.untag a.payload=`List[`String"linked-program-capture-fragmented-v4";
          `String Sys.ocaml_version;`String(string_of_int Sys.word_size);`String(string_of_bool Sys.big_endian)])
          "old header explicit";
        check(K.untag b.payload=`List[`String v5_policy;`String Sys.ocaml_version;
          `String(string_of_int Sys.word_size);`String(string_of_bool Sys.big_endian)])"V5 header explicit")
      else v5_same[a][b])(List.rev !old)decoded;
    let binding=Option.get case.ss_verifier_scope in
    List.iter(fun(field,expected)->
      let route=["only_specs";"0";"p";"0";"spec_sspecs";"0";"ss_verifier_scope";"some";field] in
      let frame=List.find(fun(f:C.frame)->f.route=route)decoded in
      check(K.equal(Expr.to_yojson expected)(K.untag frame.payload))"private source-target identity")
      ["vsb_source",binding.vsb_source;"vsb_target",binding.vsb_target]) ["linked";"post-logic"];
  let frame=v5_frame 0 ["";"\000\255";""] in
  v5_same[frame](v5_decode "linked"(v5_wire "linked"[frame]))
let v5_savings () =
  let prefix=["procs";"0";String.make 128 'k';"0";"proc_spec";"some";"spec_sspecs";"0";"ss_pre";"assertion"] in
  let frames=List.init 24(fun i->v5_frame i(prefix@[string_of_int i;"outs"])) in
  let wire=v5_wire "linked" frames in v5_same frames(v5_decode "linked" wire);
  let bytes xs=List.fold_left(fun n j->n+String.length(Yojson.Safe.to_string j)+1)0 xs in
  let absolute=List.map v5_absolute frames in
  check(bytes wire<bytes absolute)"same logical fixture has strictly fewer total wire bytes";
  check(bytes(List.map v5_code wire)<bytes(List.map v5_code absolute))"route-only byte reduction measured";
  let small=[v5_frame 0 [];v5_frame 1 ["x"];v5_frame 2 ["x"]] in
  let encoded=v5_wire "linked" small in
  List.iter2(fun f j->check(v5_code j=v5_code(v5_absolute f))"nonbenefit/tie chooses absolute")small encoded;
  check(String.length(Yojson.Safe.to_string(`List[`String(K.hex "x")]))=
    String.length(Yojson.Safe.to_string(`List[`Int 1;`List[]])))"explicit serialized tie";
  v5_same small(v5_decode "linked" encoded)
let v5_bad_states () =
  let first=v5_frame 0 ["long-prefix"] and second=v5_frame 1 ["long-prefix"] in
  let wire=v5_wire "linked"[first;second] in let seed=List.hd wire and good=List.nth wire 1 in
  let pack code=v5_pack "linked" 1 "boundary" code second.payload in
  let bad=[
    "V5 route prefix",pack(`List[`Int(-1);`List[]]);
    "V5 route prefix",pack(`List[`Int 2;`List[]]);
    "V5 noncanonical route code",pack(`List[`Int 0;`List[`String(K.hex "long-prefix")]]);
    "V5 noncanonical route code",v5_absolute second;
    "noncanonical hex",pack(`List[`Int 0;`List[`String"AA"]]);
    "hex byte budget",pack(`List[`Int 0;`List[`String"0"]]);
    "V5 route code",pack(`List[`Bool true]);
    "V5 compact tuple schema",`List[`Int 4;`String"linked";`Int 1;`String"boundary";`List[];second.payload];
    "V5 compact tuple schema",`List[`Int 5;`Int 1;`String"linked";`String"boundary";`List[];second.payload];
    "V5 compact tuple schema",`List[`Int 5;`String"linked";`Int 1;`String"boundary";`List[]];
    "V5 route phase",v5_pack "post-logic" 1 "boundary"(v5_code good)second.payload;
    "V5 route sequence",v5_pack "linked" 2 "boundary"(v5_code good)second.payload] in
  List.iter(fun(reason,bad)->let decoder=C.V5_route.decoder ~phase:"linked" in
    ignore(C.V5_route.decode decoder seed);
    v5_expect reason(fun()->ignore(C.V5_route.decode decoder bad));
    v5_expect "V5 route state poisoned"(fun()->ignore(C.V5_route.decode decoder good)))bad;
  let decoder=C.V5_route.decoder ~phase:"linked" in
  v5_expect "V5 route prefix"(fun()->ignore(C.V5_route.decode decoder good));
  let encoder=C.V5_route.encoder ~phase:"linked" in
  v5_expect "V5 route sequence"(fun()->ignore(C.V5_route.encode encoder second));
  v5_expect "V5 route state poisoned"(fun()->ignore(C.V5_route.encode encoder first));
  let encoder=C.V5_route.encoder ~phase:"post-logic" in
  v5_expect "V5 route phase"(fun()->ignore(C.V5_route.encode encoder first));
  v5_expect "V5 route phase"(fun()->ignore(C.V5_route.decoder ~phase:"unknown"));
  let tie=v5_wire "linked"[v5_frame 0 ["x"];v5_frame 1 ["x"]] in
  let decoder=C.V5_route.decoder ~phase:"linked" in ignore(C.V5_route.decode decoder(List.hd tie));
  v5_expect "V5 noncanonical route code"(fun()->ignore(C.V5_route.decode decoder
    (v5_pack "linked" 1 "boundary"(`List[`Int 1;`List[]])(K.tag(`Int 1)))))
let v5_grammar () =
  let prog,_=fixture() in let frames=v5_collect "linked" prog in
  let wire=v5_wire "linked" frames in
  C.validate_frames ~version:5(v5_decode "linked" wire);
  let duplicate=List.hd wire::wire in
  v5_expect "V5 route sequence"(fun()->ignore(v5_decode "linked" duplicate));
  v5_expect "V5 route sequence"(fun()->ignore(v5_decode "linked"(List.tl wire)));
  let swapped=match wire with a::b::rest->b::a::rest|_->Alcotest.fail "fixture frames" in
  v5_expect "V5 route sequence"(fun()->ignore(v5_decode "linked" swapped));
  let no_footer=List.rev(List.tl(List.rev frames)) in
  v5_expect "missing frame"(fun()->C.validate_frames ~version:5(v5_decode "linked"(v5_wire "linked" no_footer)));
  let bad=List.map(fun(f:C.frame)->if f.kind="footer" then{f with payload=K.tag(`Int(-1))}else f)frames in
  v5_expect "footer frame count"(fun()->C.validate_frames ~version:5(v5_decode "linked"(v5_wire "linked" bad)));
  let bad=List.mapi(fun i(f:C.frame)->if i=1 then{f with kind="header"}else f)frames in
  v5_expect "frame order/kind/route"(fun()->C.validate_frames ~version:5(v5_decode "linked"(v5_wire "linked" bad)))
let v5_line_caps () =
  let payload total=`List[`List(List.init 64(fun _->`Int 0));
    `String(String.make(total/2)'x');`String(String.make(total-total/2)'y')] in
  let base={C.phase="linked";seq=0;kind="boundary";route=[];payload=payload 0} in
  let cap=K.fragment_bytes in
  let expanded f=String.length(Yojson.Safe.to_string(C.frame_json ~version:4 f))+1 in
  let total=cap-expanded base in
  let exact={base with payload=payload total} in
  check(expanded exact=cap)"expanded full-line exact boundary including LF";
  let encoder=C.V5_route.encoder ~phase:"linked" in
  let wire=C.V5_route.encode encoder exact in
  check(String.length(Yojson.Safe.to_string wire)+1<=cap)"compact full line cap";
  v5_same[exact](v5_decode "linked"[wire]);
  let over={base with payload=payload(total+1)} in
  v5_expect "capture frame1MiB cap"(fun()->ignore(C.V5_route.encode(C.V5_route.encoder ~phase:"linked")over));
  let overhead=String.length(Yojson.Safe.to_string(v5_pack "linked" 0 "boundary"(`List[])(payload 0)))+1 in
  let compact total=v5_pack "linked" 0 "boundary"(`List[])(payload total) in
  let at=compact(cap-overhead) in
  check(String.length(Yojson.Safe.to_string at)+1=cap)"compact exact LF boundary";
  v5_expect "capture frame1MiB cap"(fun()->ignore(C.V5_route.decode(C.V5_route.decoder ~phase:"linked")at));
  let over=compact(cap-overhead+1) in
  check(String.length(Yojson.Safe.to_string over)+1=cap+1)"compact one-over includes LF";
  let decoder=C.V5_route.decoder ~phase:"linked" in
  v5_expect "capture frame1MiB cap"(fun()->ignore(C.V5_route.decode decoder over));
  v5_expect "V5 route state poisoned"(fun()->ignore(C.V5_route.decode decoder wire))
let v5_bounds () =
  let parity f=let why=incomplete_reason(fun()->f 4) in v5_expect why(fun()->f 5) in
  parity(fun version->ignore(C.checked ~version C.jstring C.string_of_json(String.make 65537 'x')));
  parity(fun version->ignore(C.checked ~version
    (fun x->`String(Int64.to_string x))
    (function `String s->Ok(Int64.of_string s)|_->Error"int64")Int64.max_int));
  let rec cycle=0::cycle in
  parity(fun version->ignore(C.checked ~version
    (fun xs->`List(List.map C.jint xs)) (C.list_of C.int_of_json)cycle));
  let rec deep n e=if n=0 then e else deep(n-1)(Expr.UnOp(Not,e)) in
  parity(fun version->ignore(C.ast ~version visit_expr Expr.to_yojson Expr.of_yojson
    (deep 2050(Expr.Lit(Literal.Bool true)))));
  parity(fun version->ignore(C.ast ~version(fun v x->v#visit_literal () x)
    Literal.to_yojson Literal.of_yojson(Literal.Int(Z.shift_left Z.one 65536))));
  parity(fun version->ignore(C.checked ~version C.jint
    (fun json->Result.map((+)1)(C.int_of_json json))7));
  let prog,_=fixture() in let pred=Hashtbl.find prog.preds "P" in
  Hashtbl.replace prog.preds "P" {pred with pred_facts=List.init 131072(fun _->Expr.Lit(Literal.Bool true))};
  let fail version=C.iter_program ~version ~annot_to_json:Annot.Basic.to_yojson
    ~annot_of_json:Annot.Basic.of_yojson ~phase:"linked" ~emit:(fun _->())prog in
  parity fail;
  let good,_=fixture() in let pred=Hashtbl.find good.preds "P" in
  Hashtbl.replace good.preds "P" {pred with pred_definitions=[None,List.init 2055(fun _->Asrt.Emp)]};
  let frames=v5_collect "linked" good in
  C.validate_frames ~version:5(v5_decode "linked"(v5_wire "linked" frames))
let v5_writer_fault mode =
  let injected=K.Incomplete("injected V5 "^mode) and attempts=ref 0 in
  let io=match mode with
    |"write"|"overflow-write"->{W.system_io with write=(fun _ _ _ _->incr attempts;raise injected)}
    |"fsync"->{W.system_io with fsync=(fun fd->if(Unix.fstat fd).Unix.st_kind=Unix.S_REG
        then(incr attempts;raise injected)else Unix.fsync fd)}
    |"close"->{W.system_io with close=(fun fd->let regular=(Unix.fstat fd).Unix.st_kind=Unix.S_REG in
        Unix.close fd;if regular then(incr attempts;raise injected))}
    |_->Alcotest.fail "V5 fault selector" in
  let prog=if mode="overflow-write" then batch_large_fixture() else fst(fixture()) in
  with_writer ~io(fun root writer->
    let session:C.session={writer;version=5;next=0;counts=[]} in
    let expected=if mode="overflow-write" then K.Incomplete("injected V5 "^mode^
      " phase=linked table=procs keyIndex=0 keyHexPrefix=70 bindingOrdinal=0")else injected in
    Alcotest.check_raises "exact V5 write/fsync/close failure"(batch_error expected)
      (fun()->v5_capture session "linked" prog);
    check(!attempts=1)"no retry";batch_failed_state root writer session;
    if mode="close" then(let _,_,dir,active,_,_,_,uncertain=W.snapshot writer in
      check(uncertain&&not dir&&not active)"V5 preserves close uncertainty");
    Alcotest.check_raises "V5 failed phase never advances"(batch_error(K.Incomplete"snapshot invocation order"))
      (fun()->v5_capture session "post-logic" prog);
    check(!attempts=1)"no later IO")
let v5_writer () =
  let prog=batch_large_fixture() in let io,writes,_=batch_observer() in
  with_writer ~io(fun root writer->
    let session:C.session={writer;version=5;next=0;counts=[]} in
    List.iteri(fun index phase->
      let frames=v5_collect phase prog in let wire=v5_wire phase frames in
      let expected=String.concat ""(List.map(fun json->Yojson.Safe.to_string json^"\n")wire) in
      v5_capture session phase prog;
      let file=Printf.sprintf "%08d.jsonl" index in
      Alcotest.(check string)"production V5 tuple bytes" expected(batch_read root file);
      let chunks=List.rev !writes|>List.filter_map(fun(name,text)->if name=file then Some text else None) in
      check(List.length chunks>=2)"actual V5 overflow batching";
      List.iter(fun chunk->check(String.length chunk<=K.fragment_bytes&&String.ends_with ~suffix:"\n" chunk)
        "complete bounded V5 batches")chunks;
      C.validate_frames ~version:5(v5_decode phase wire);
      check(List.nth session.counts index=List.length frames)"real V5 frame counts") ["linked";"post-logic"];
    let manifest=`Assoc["schema",`Int 5;"codecPolicy",`String v5_policy;
      "phaseFiles",`List[`String"00000000.jsonl";`String"00000001.jsonl"];
      "frameCounts",`List(List.map(fun n->`Int n)session.counts);
      "requiresNativeSuccessAndClosedWriter",`Bool true;"proofAccepted",`Bool false] in
    Alcotest.(check string)"production V5 closed manifest"(Yojson.Safe.to_string manifest^"\n")
      (batch_read root "00000002.jsonl");
    let failure,sealed,dir,active,intended,written,phases,uncertain=W.snapshot writer in
    let bytes=List.fold_left(fun n file->n+String.length(batch_read root file))0
      ["00000000.jsonl";"00000001.jsonl";"00000002.jsonl"] in
    check(failure=None&&sealed&&dir&&active&&phases=3&&not uncertain&&
      intended=written&&written=Int64.of_int bytes)"V5 Writer certainty and accounting unchanged");
  List.iter v5_writer_fault["write";"overflow-write";"fsync";"close"];
  with_writer ~limit:262144L(fun root writer->
    let session:C.session={writer;version=5;next=0;counts=[]} in
    Alcotest.check_raises "actual V5 prospective physical cap remains enforced"
      (batch_error(K.Incomplete"capture prospective physical cap phase=linked table=procs keyIndex=0 keyHexPrefix=70 bindingOrdinal=0"))
      (fun()->v5_capture session "linked" prog);
    check(session.next=0&&not(Sys.file_exists(Filename.concat root"00000002.jsonl")))"cap failure has no manifest")
let v5_legacy () =
  check(C.version_of_policy(Some v5_policy)=5)"explicit V5 policy";
  let prog,_=fixture() in
  List.iter(fun version->
    let io,writes,_=batch_observer() in
    with_writer ~io(fun _ writer->
      let session:C.session={writer;version;next=0;counts=[]} in
      List.iteri(fun index phase->
        let expected=batch_lines version phase prog in
        let old=List.map(fun text->C.frame_of_json ~version(Yojson.Safe.from_string text))expected in
        C.validate_frames ~version old;
        batch_capture session phase prog;
        let file=Printf.sprintf "%08d.jsonl" index in
        let actual=List.rev !writes|>List.filter_map(fun(name,text)->if name=file then Some text else None) in
        if version=4 then check(actual=[String.concat "" expected])"V4 unchanged batch IO"
        else check(actual=expected)"V1-3 unchanged per-frame IO") ["linked";"post-logic"])) [1;2;3;4];
  let frame=v5_frame 0 [] in
  v5_expect "V5 requires stateful route transport"(fun()->ignore(C.frame_json ~version:5 frame));
  v5_expect "V5 requires stateful route transport"(fun()->ignore(C.frame_of_json ~version:5(`List[])));
  let tuple=List.hd(v5_wire "linked"[frame]) in
  List.iter(fun version->v5_expect "frame exact schema/order"(fun()->ignore(C.frame_of_json ~version tuple))) [1;2;3;4];
  let frames=v5_collect "linked" prog in
  v5_expect "header ABI"(fun()->C.validate_frames ~version:4 frames)

let tests = List.map(fun(name,f)->Alcotest.test_case name `Quick f)[
  "V4 all14/7/7 typed fields atoms options and private identity",v4_fields;
  "V4 long containers versus whole Expr depth",v4_flat_and_depth;
  "V4 original-parent aggregate/cycle/Z bounds",v4_aggregate;
  "V4 own-fingerprinted grammar and expected-original corruption",v4_grammar;
  "V4 explicit policy and unchanged closed writer",v4_policy_and_phases;
  "final scope GIL/JSON/linked roundtrip",scope_roundtrip;
  "final scope defaults identity and malformed/orphan rejection",scope_defaults_and_rejections;
  "final scope alpha/normalization and caller separation",scope_alpha_and_private_posts;
  "binary64 bit payloads and corruption",floats;
  "all tagged constructors and raw key bytes",bytes;
  "typed Z/Number/UTF16 literals",literals;
  "pre-conversion cycle/closure/custom/budget rejection",budgets;
  "all tables ten proc fields triples PHI and actual predecessors",structure;
  "missing duplicate reordered wrong-kind frames",framing;
  "enabled both phases preserve actual values",enabled_same_values;
  "complete duplicate table and predecessor inventories",duplicate_bindings;
  "actual short-write complete fsync/close",writer_success;
  "zero-write permanent latch",writer_fault "zero";
  "fsync failure permanent latch",writer_fault "fsync";
  "close failure permanent latch",writer_fault "close";
  "fragment cumulative and physical cap tightening",writer_caps;
  "exclusive existing file remains intact",writer_exclusive;
  "named root identity substitution",writer_substitution;
  "post-fsync allocation refresh",post_fsync_allocation;
  "disabled has no traversal or conversion",disabled;
  "V2 generic derived-only policy exact roundtrip",v2_derived;
  "V2 native phases schema header manifest and unchanged values",v2_phases;
  "V2 explicit negotiation and invalid versions",v2_negotiation;
  "V2 unchanged typed aggregate byte and frame bounds",v2_limits;
  "V3 real typed crossing and complete standard roundtrip",v3_typed_crossing;
  "V3 whole predicate command and closed two-phase capture",v3_phases;
  "V3 original decoded typed and security bounds",v3_security;
  "V3 finite transport eligibility and unchanged byte caps",v3_transport_limits;
  "V3 explicit negotiation and cross-policy rejection",v3_negotiation;
  "V3 typed physical depth2048 and legacy512 boundaries",v3_typed_depth;
  "V4 batches preserve bytes caps and phase closure",batch_identity_and_closure;
  "V4 individual frame envelope including newline cap",batch_individual_frame_cap;
  "V4 phase flush exact write failure without manifest",batch_failure "phase-write";
  "V4 overflow flush exact write failure without manifest",batch_failure "overflow-write";
  "V4 batched fsync failure without manifest",batch_failure "fsync";
  "V4 phase close uncertainty without manifest",batch_failure "close";
  "V1 V2 V3 per-frame IO remains unchanged",batch_legacy_io
]

  @ List.map(fun(name,f)->Alcotest.test_case name `Quick f)[
    "V5 full logical typed private and raw-route roundtrip",v5_roundtrip;
    "V5 measured compact route savings and canonical fallback",v5_savings;
    "V5 exact malformed tuple delta and poisoned states",v5_bad_states;
    "V5 dense transport and real complete frame grammar",v5_grammar;
    "V5 expanded and compact complete-line caps including LF",v5_line_caps;
    "V5 unchanged parent leaf depth Z custom cycle identity bounds",v5_bounds;
    "V5 actual Writer batches manifest caps and exact faults",v5_writer;
    "V5 legacy1-4 IO bytes stateless and cross-policy behavior",v5_legacy
  ]
