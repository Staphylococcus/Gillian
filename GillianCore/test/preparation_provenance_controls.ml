(* Standalone controls: deliberately absent from run_tests and its registry. *)
open Gil_syntax
module P = Engine.Preparation_provenance
module C = Linked_program_capture.Codec
module SS = Utils.Containers.SS
let check label value = Alcotest.(check bool) label true value
let field key = function
  | `Assoc xs -> Option.value ~default:`Null (List.assoc_opt key xs)
  | _ -> `Null
let data row = C.untag (field "data" row)
let rows lines = List.rev_map Yojson.Safe.from_string !lines
let run ?bytes ?events ?record ?carriers f =
  let lines = ref [] in
  let result, session, receipts = P.For_tests.run ?bytes ?events ?record ?carriers
    (fun text -> lines := text :: !lines) (fun s -> P.observe (fun _ -> f s)) in
  result, session, receipts, rows lines
let pre = [Asrt.Emp], None
let source s ?(kind="procedure") ?(name="selected") count =
  s.P.procedures <- (if kind="procedure" then SS.singleton name else SS.empty);
  s.P.lemmas <- (if kind="lemma" then SS.singleton name else SS.empty);
  ignore (P.add_source s kind name count)
let group ?(kind="procedure") ?(name="selected") parent carriers =
  P.register_group kind name parent pre
    (List.map (fun c -> c, pre, [pre]) carriers)
let prepare ?(kind="procedure") ?(name="selected") ?(verify=true) carrier count =
  let origin = P.origin kind name carrier in
  P.normalised origin ~to_verify:verify (fun () -> count) "ok";
  for i=0 to count-1 do
    P.snapshot origin ~id:(0,i) ~phase:"normalized-state" (fun () -> `String "actual-state");
    if verify then P.snapshot origin ~id:(0,i) ~phase:"test-created"
      (fun () -> `String "actual-test-state")
  done
let complete receipts = List.exists fst receipts
let disabled () =
  let previous = !P.current and called = ref false in
  Fun.protect ~finally:(fun () -> P.current := previous) (fun () ->
    P.current := None;
    P.observe (fun _ -> called:=true);
    P.snapshot None ~id:(0,0) ~phase:"normalized-state" (fun () -> called:=true; `Null);
    P.normalised None ~to_verify:true (fun () -> called:=true; 0) "disabled";
    check "unselected kind/name has no capture branch" (not(P.captures "lemma" "unselected"));
    check "disabled hooks do not evaluate payloads" (not !called))
let exact_mapping () =
  let a=ref 7 and b=ref 7 in
  let _,s,receipts,lines = run (fun s ->
    source s ~kind:"lemma" 2;
    group ~kind:"lemma" 0 [];
    group ~kind:"lemma" 1 [a;b];
    prepare ~kind:"lemma" a 2;
    prepare ~kind:"lemma" b 1;
    P.finish ~procedure_tests:0 ~lemma_tests:3) in
  check "two identical values retain distinct physical carriers" (a != b);
  check "zero and two expansions both complete" (s.P.failed=None && complete receipts);
  let groups=List.filter (fun r -> field "event" r=`String "expanded-parent") lines in
  check "explicit raw-parent/output cardinalities retained"
    (List.map (fun r -> field "raw_parent" (data r),field "output_count" (data r)) groups
      =[(`Int 0,`Int 0);(`Int 1,`Int 2)]);
  let states=List.filter (fun r -> field "event" r=`String "normalized-state") lines in
  check "native lemma ids remain unchanged while expanded ordinals differ"
    (List.map (fun r -> field "expanded" (data r),field "native_id" (data r)) states
      =[(`Int 0,`List [`Int 0;`Int 0]);(`Int 0,`List [`Int 0;`Int 1]);
        (`Int 1,`List [`Int 0;`Int 0])]);
  check "native final total is exact" (field "total_tests" (List.hd (List.rev lines))=`Int 3)
let zero_normalized () =
  let carrier=ref 0 in
  let _,s,receipts,_=run (fun s -> source s 1;group 0 [carrier];
    prepare carrier 0;P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "zero normalization is explicitly captured, with no proof credit"
    (s.P.failed=None && complete receipts)
let unverified () =
  let carrier=ref 0 in
  let _,s,receipts,_=run (fun s -> source s 1;group 0 [carrier];
    prepare ~verify:false carrier 2;P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "non-test normalization has complete coverage and zero test total"
    (s.P.failed=None && complete receipts)
let duplicate_carrier () =
  let a=ref 0 in
  let _,s,receipts,_=run (fun s -> source s 1;group 0 [a;a];
    P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "duplicate physical carriers fail closed" (s.P.failed<>None && not(complete receipts))
let missing_and_totals () =
  List.iter (fun bad_total ->
    let a=ref 0 in
    let _,s,receipts,_=run (fun s -> source s 1;group 0 [a];
      if bad_total then prepare a 1;
      P.finish ~procedure_tests:(if bad_total then 2 else 0) ~lemma_tests:0) in
    check "missing carrier or incorrect native total cannot complete"
      (s.P.failed<>None && not(complete receipts))) [false;true]
let limits () =
  List.iter (fun mode ->
    let a=ref 0 in
    let _,s,receipts,lines=run
      ~bytes:(if mode="bytes" then 4096 else P.max_bytes)
      ~events:(if mode="events" then 1 else P.max_events)
      ~record:(if mode="record" then 32 else P.max_record)
      ~carriers:(if mode="carriers" then 0 else P.max_carriers)
      (fun s -> source s 1;group 0 [a]) in
    check (mode ^ " cap cannot qualify") (s.P.failed<>None && not(complete receipts));
    check "no partial record marked complete" (List.for_all
      (fun r -> field "complete" r<>`Bool true) lines)) ["bytes";"events";"record";"carriers"]
let serializer_and_io () =
  let _,s,receipts,_=run (fun _ -> P.observe (fun _ -> failwith "serializer")) in
  check "serialization exception is explicit incomplete" (s.P.failed<>None && not(complete receipts));
  let _,s,receipts=P.For_tests.run (fun _ -> failwith "IO") (fun _ ->
    P.observe (fun s -> P.emit s "event" (fun () -> `Null))) in
  check "write failure cannot produce completion receipt" (s.P.failed<>None && not(complete receipts))
let private_directory f =
  let directory=Filename.temp_file "gillian-preparation-" "" in
  Sys.remove directory;Unix.mkdir directory 0o700;
  Fun.protect ~finally:(fun () ->
    Array.iter (fun name -> Sys.remove(Filename.concat directory name)) (Sys.readdir directory);
    Unix.rmdir directory) (fun () -> f directory)
let stale_output () = private_directory (fun directory ->
  let path=Filename.concat directory "stale.jsonl" in
    let channel=open_out_bin path in output_string channel "retained";close_out channel;
    check "existing output rejected" (P.open_runtime path=None);
    let channel=open_in_bin path in
    let retained=Fun.protect ~finally:(fun () -> close_in channel)
      (fun () -> really_input_string channel 8) in
    check "existing output remains byte-exact" (retained="retained"))
let output_parent_scope () = private_directory (fun directory ->
  let alias=Filename.concat directory "alias" in
  Unix.symlink directory alias;
  check "symlinked parent rejected"
    (P.open_runtime (Filename.concat alias "rejected.jsonl")=None);
  check "symlinked path created no output" (not(Sys.file_exists(Filename.concat directory "rejected.jsonl")));
  Unix.chmod directory 0o755;
  check "nonprivate immediate parent rejected"
    (P.open_runtime (Filename.concat directory "public-parent.jsonl")=None);
  Unix.chmod directory 0o700;
  let path=Filename.concat directory "fresh.jsonl" in
  match P.open_runtime path with
  | None -> failwith "valid canonical private parent rejected"
  | Some s -> P.close s;
      let info=Unix.lstat path in
      check "fresh private output uses regular0600 single-link file"
        (info.Unix.st_kind=Unix.S_REG && info.st_perm land 0o777=0o600 && info.st_nlink=1))
let state_custom_guard () =
  let z=Z.shift_left Z.one 100 in
  let expression=Expr.Lit (Literal.Int z) in
  let state=ref expression and converted=ref false in
  ignore (P.guarded_state ~projection:state ~assertions:(fun () -> [Asrt.Pure expression])
    ~to_json:(fun () -> converted:=true;Expr.to_yojson !state));
  check "typed bounded integer permits actual state serializer" !converted;
  converted:=false;
  let rejected=try ignore (P.guarded_state ~projection:state
      ~assertions:(fun () -> [Asrt.Emp])
      ~to_json:(fun () -> converted:=true;`Null));false
    with C.Incomplete _ -> true in
  check "omitted custom field rejected before serializer" (rejected && not !converted);
  let huge=Expr.Lit (Literal.Int (Z.shift_left Z.one 65537)) in
  let rejected=try ignore(P.guarded_state ~projection:huge
      ~assertions:(fun () -> [Asrt.Pure huge]) ~to_json:(fun () -> converted:=true;`Null));false
    with C.Incomplete _ -> true in
  check "integer bit overflow rejected before conversion" (rejected && not !converted)
let integer_conversion_budget () =
  let z=Expr.Lit (Literal.Int (Z.shift_left Z.one 32768)) in
  let expression=Expr.EList (List.init 40 (fun _ -> z)) in
  let converted=ref false in
  let rejected=try ignore(P.guarded_state ~projection:expression
      ~assertions:(fun () -> [Asrt.Pure expression])
      ~to_json:(fun () -> converted:=true;`Null));false
    with C.Incomplete _ -> true in
  check "aggregate integer conversion is bounded before serialization"
    (rejected && not !converted)
let selection () =
  let module V=Utils.Config.Verification in
  let saved= !V.things_to_verify,!V.procs_to_verify,!V.lemmas_to_verify,!V.things_to_exclude in
  Fun.protect ~finally:(fun () -> let mode,ps,ls,excluded=saved in
    V.things_to_verify:=mode;V.procs_to_verify:=ps;V.lemmas_to_verify:=ls;
    V.things_to_exclude:=excluded) (fun () ->
    V.things_to_verify:=V.Specific;V.procs_to_verify:=["a";"missing"];
    V.lemmas_to_verify:=["l"];V.things_to_exclude:=SS.singleton "l";
    let ps,ls=P.select_procs_and_lemmas ~procs_to_verify:(SS.of_list ["a";"b"])
      ~lemmas_to_verify:(SS.singleton "l") in
    check "original intersection/exclusion selection preserved" (SS.equal ps (SS.singleton "a") && SS.is_empty ls))
let aggregate_rejected value =
  try ignore (P.inspect_aggregate P.Expanded_parent value); false
  with C.Incomplete _ -> true
let aggregate_flat_containers () =
  let wide = List.init 1024 (fun _ -> 0) in
  let legacy_rejected = try ignore (C.inspect wide); false
    with C.Incomplete _ -> true in
  check "legacy physical list-spine depth is exercised" legacy_rejected;
  check "wide flat aggregate admitted without raising occurrence/word/string bounds"
    (not (aggregate_rejected wide));
  check "exact32768 occurrences admitted"
    (not (aggregate_rejected (Array.make 32767 0)));
  check "one extra occurrence rejected"
    (aggregate_rejected (Array.make 32768 0));
  check "exact262144 words admitted"
    (not (aggregate_rejected (Array.create_float 262143)));
  check "one extra word rejected"
    (aggregate_rejected (Array.create_float 262144));
  check "exact65536 string bytes admitted"
    (not (aggregate_rejected (String.make 65536 'x')));
  check "one extra single-string byte rejected"
    (aggregate_rejected (String.make 65537 'x'))
let aggregate_combined_alias_limits () =
  let a = Array.make 17000 0 and b = Array.make 17000 0 in
  check "individual aggregates fit the old occurrence limit"
    (not (aggregate_rejected a) && not (aggregate_rejected b));
  check "combined aggregate cannot reset its occurrence counter"
    (aggregate_rejected [a;b]);
  check "repeated physical aliases are charged by occurrence"
    (aggregate_rejected [a;a]);
  let chunk = String.make 65536 'x' in
  check "exact262144 aggregate string bytes admitted including aliases"
    (not (aggregate_rejected [chunk;chunk;chunk;chunk]));
  check "repeated alias exceeds unchanged aggregate string limit"
    (aggregate_rejected [chunk;chunk;chunk;chunk;chunk]);
  let _,s,receipts,lines = run (fun _ ->
    ignore (P.inspect_aggregate P.Expanded_parent [a;a])) in
  check "aggregate limit keeps incomplete terminal behavior"
    (s.P.failed<>None && not (complete receipts) &&
     List.for_all (fun row -> field "complete" row<>`Bool true) lines)
let aggregate_cycles_and_host_shapes () =
  let rec cyclic = 0 :: cyclic in
  check "active-path cycle rejected before serialization" (aggregate_rejected cyclic);
  check "host closure rejected before serialization"
    (aggregate_rejected (fun x -> x + 1));
  let z = Z.shift_left Z.one 100 in
  let found = P.inspect_aggregate P.Expanded_parent z in
  check "custom blocks discovered without casting or converting"
    (List.exists (fun raw -> raw == Obj.repr z) found)
let unchanged_ast_and_transport_guards () =
  let wide = List.init 4096 (fun _ -> Asrt.Emp) in
  check "wide AST container admitted by aggregate preflight"
    (not (aggregate_rejected wide));
  let _,s,receipts,_ = run (fun s ->
    P.emit s "wide-pre" (fun () -> P.ast wide)) in
  check "full AST serialization still requires unchanged guard_ast_v3"
    (s.P.failed<>None && not (complete receipts));
  let payload = `List (List.init 4096 (fun _ -> `Null)) in
  check "wide JSON aggregate itself remains bounded and admitted"
    (not (aggregate_rejected payload));
  let _,s,receipts,_ = run (fun s ->
    P.emit s "wide-transport" (fun () -> payload)) in
  check "full emit still requires unchanged transport guard"
    (s.P.failed<>None && not (complete receipts))
let expanded_payload_ownership () =
  let small = Spec.s_init pre [pre] None Flag.Normal true in
  let large = { small with Spec.ss_label = Some (String.make 65537 'x', []) } in
  let capture carrier =
    let _,s,receipts,lines = run (fun s ->
      source s 1;
      P.spec_group "selected" 0 pre [carrier];
      prepare carrier 1;
      P.finish ~procedure_tests:1 ~lemma_tests:0) in
    check "actual spec identity joins normalization and test completion"
      (s.P.failed=None && complete receipts);
    List.filter_map (fun row ->
      if field "event" row=`String "expanded-parent" then Some (data row)
      else None) lines
  in
  let ordinary = capture small and opaque = capture large in
  check "oversized carrier-only label changes no emitted field"
    (List.length ordinary=1 && ordinary=opaque);
  let _,s,receipts,_ = run (fun s ->
    source s 1;P.spec_group "selected" 0 pre [large;large]) in
  check "opaque handles still reject duplicate physical identity"
    (s.P.failed=Some "ambiguous-physical-carrier" && not (complete receipts))
let expanded_whole_event_budget () =
  let expected = Some "aggregate:expanded-parent: aggregate occurrence budget32768" in
  let reject input outputs =
    let _,s,receipts,_ = run (fun s ->
      source s 1;P.spec_group "selected" 0 input outputs) in
    check "complete emitted projection shares the unchanged occurrence budget"
      (s.P.failed=expected && not (complete receipts))
  in
  let wide = List.init 6000 (fun _ -> Asrt.Emp), None in
  (* Each located root is below32768; input plus output PRE and POST is not.
     Omitting input, resetting counters, or counting an alias once fails this. *)
  reject wide [Spec.s_init wide [wide] None Flag.Normal true];
  let shared = List.init 3000 (fun _ -> Asrt.Emp), None in
  let outputs = List.init 6 (fun _ ->
    Spec.s_init shared [] None Flag.Normal true) in
  reject pre outputs
let expanded_empty_and_carrier_admission () =
  let _,s,receipts,lines = run (fun s ->
    source s 1;P.spec_group "selected" 0 pre [];
    P.finish ~procedure_tests:0 ~lemma_tests:0) in
  let groups = List.filter (fun row ->
    field "event" row=`String "expanded-parent") lines in
  check "zero expansion preserves its admitted input and explicit empty output"
    (s.P.failed=None && complete receipts &&
     List.map (fun row -> let d=data row in
       field "input_pre" d<>`Null && field "output_count" d=`Int 0 &&
       field "outputs" d=`List []) groups=[true]);
  let oversized_input = List.init 17000 (fun _ -> Asrt.Emp), None in
  let _,s,receipts,_ = run (fun s ->
    source s 1;P.spec_group "selected" 0 oversized_input []) in
  check "zero expansion cannot bypass input admission"
    (s.P.failed=Some "aggregate:expanded-parent: aggregate occurrence budget32768" &&
     not (complete receipts));
  let a=Spec.s_init pre [] None Flag.Normal true in
  let b=Spec.s_init pre [] None Flag.Normal true in
  let _,s,receipts,_ = run ~carriers:2 (fun s ->
    source s 2;P.spec_group "selected" 0 pre [a;b];
    P.spec_group "selected" 1 oversized_input [a]) in
  check "remaining carrier registry is bounded before projection traversal"
    (s.P.failed=Some "expanded-carrier-cap" && not (complete receipts))

(* v2 controls below are source-only in this candidate. Original twenty function
   bodies and registry entries above/below remain byte-for-byte donor text. *)
module F = Engine.Preparation_framing
let run_framed ?bytes ?events ?record f =
  let lines=ref [] in
  let result,s,receipts=P.For_tests.run ~framed:true ?bytes ?events ?record
    (fun text -> lines:=text:: !lines) (fun s -> P.observe(fun _ -> f s)) in
  result,s,receipts,rows lines
let logical_rows physical =
  let chunk=Buffer.create 16384 and result=ref [] in
  List.iter(fun row -> match field "event" row with
    | `String "frame" -> (match field "bytes" row with
        | `String bytes -> Buffer.add_string chunk bytes | _ -> assert false)
    | `String "commit" ->
        result:=Yojson.Safe.from_string(Buffer.contents chunk):: !result;Buffer.clear chunk
    | _ -> ())physical;
  check "no uncommitted bytes exposed by control" (Buffer.length chunk=0);
  List.rev !result
let framing_exact_grammar () =
  let value=`Assoc["duplicate",`Tuple[`Float 0.;`Float (-0.);`String "\000\255"];
    "duplicate",`Variant("x\000",Some(`Intlit "000123"));
    "empty",`Variant("none",None);"bool",`Bool true;"null",`Null] in
  let buffer=Buffer.create 64 in
  F.json value (F.create(Buffer.add_string buffer));
  check "stream equals exact existing tagged bytes including duplicate keys/bothzero"
    (Buffer.contents buffer=Yojson.Safe.to_string(C.tag value));
  let _,s,receipts,physical=run_framed(fun s ->
    P.emit s "fixture" (fun () -> value);P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "framed exact logical data completes" (s.P.failed=None && complete receipts);
  check "same tagged logical content" (List.map data(logical_rows physical)=[value])
let framing_exact_word_meter () =
  let alias=`String "\000\255abcdefgh" in
  let fixtures=[`Null;`Bool false;`Bool true;`Int 0;`Int (-7);`Intlit "001";
    `Float 0.;`Float (-0.);`String "";`String "1234567";`String "12345678";
    `List[];`Tuple[];`Assoc[];`List[alias;alias];`Tuple[`Int 0;alias];
    `Variant("n",None);`Variant("n",Some alias);
    `Assoc["dup",alias;"dup",alias]] in
  let exact shape words =
    ignore(C.inspect ~node_limit:100000 ~word_limit:words ~depth_limit:10000
      ~string_limit:524288 ~string_total:1048576 shape);
    if words>0 then check "one fewer host word must reject exact virtual charge"
      (try ignore(C.inspect ~node_limit:100000 ~word_limit:(words-1) ~depth_limit:10000
        ~string_limit:524288 ~string_total:1048576 shape);false
       with C.Incomplete _ -> true) in
  List.iter(fun value ->
    let t=F.create(fun _ -> ()) in F.json value t;
    exact value t.F.raw.words;exact(C.tag value)t.F.tagged.words)fixtures;
  (* Also check the streaming constructor path, separate from F.json replay. *)
  let value=`Assoc["k",`List[`Bool true;`Variant("n",Some alias)]] in
  let t=F.create(fun _ -> ()) in
  F.fields["k",F.values[F.bool true;F.variant "n"(Some(F.bytes "\000\255abcdefgh"))]]t;
  exact value t.F.raw.words;exact(C.tag value)t.F.tagged.words
let framing_large_multiplicity () =
  let shared=List.init 1500(fun _ -> Asrt.Emp),None in
  let carriers=List.init 6(fun _ -> Spec.s_init shared [shared] None Flag.Normal true) in
  let old_failed=try ignore(P.inspect_aggregate P.Expanded_parent
    (shared,List.map(fun (c:Spec.st) -> c.ss_pre,c.ss_posts)carriers));false
    with C.Incomplete _ -> true in
  check "fixture really exceeds old32768 whole group" old_failed;
  let _,s,receipts,physical=run_framed(fun s ->
    source s 2;
    P.emit s "original-parent"(fun () -> `Assoc["pre",P.located shared]);
    P.spec_group "selected" 0 shared carriers;
    P.spec_group "selected" 1 shared [];
    List.iteri(fun id carrier ->
      let o=P.origin "procedure" "selected" carrier in
      P.normalised o ~to_verify:true(fun () -> 1)"ok";
      P.snapshot o ~id:(id,0) ~phase:"normalized-state"(fun () -> `String "normalized");
      P.snapshot o ~id:(id,0) ~phase:"test-created"(fun () -> `String "test-distinct"))carriers;
    P.finish ~procedure_tests:6 ~lemma_tests:0) in
  check "overold whole group completes with retained individual bounds"
    (s.P.failed=None && complete receipts);
  let logical=logical_rows physical in
  let groups=List.filter(fun r -> field "event" r=`String "expanded-parent")logical in
  let expected=P.located shared in
  check "input and all six ordered alias PRE/POST occurrences survive frame boundaries"
    (match groups with [large;zero] ->
      let large=data large and zero=data zero in
      field "input_pre" large=expected && field "input_pre" zero=expected &&
      field "outputs" zero=`List [] &&
      (match field "outputs" large with `List xs ->
        List.length xs=6 && List.for_all(fun x ->
          field "pre" x=expected && field "posts" x=`List[expected])xs | _ -> false)
      | _ -> false);
  check "distinct normalized and test states retained"
    (List.filter_map(fun r -> match field "event" r with
      | `String "normalized-state" -> Some(field "payload"(data r)) | _ -> None)logical
      =List.init 6(fun _ -> `String "normalized") &&
     List.filter_map(fun r -> match field "event" r with
      | `String "test-created" -> Some(field "payload"(data r)) | _ -> None)logical
      =List.init 6(fun _ -> `String "test-distinct"));
  check "logical and physical counters differ" (s.P.events>s.P.logical_events);
  check "every decoded frame bounded16KiB" (List.for_all(fun r ->
    if field "event" r=`String "frame" then match field "length" r with
    | `Int n -> n>0 && n<=16384 | _ -> false else true)physical)
let framing_shared_limits () =
  let reject f=let _,s,receipts,_=run_framed f in
    check "shared overflow cannot qualify" (s.P.failed<>None && not(complete receipts)) in
  let text=String.make 65536 'x' in
  reject(fun _ -> ignore(P.inspect_aggregate P.Expanded_parent [text;text;text;text;text]));
  reject(fun _ -> ignore(P.inspect_aggregate P.Expanded_parent
    [Array.make 140000 0;Array.make 140000 0]));
  reject(fun s -> P.emit_framed s "transport-strings"
    (F.list(fun add -> for _=1 to 9 do add(F.bytes text) done)));
  reject(fun s -> P.emit_framed s "transport-words"
    (F.list(fun add -> for _=1 to 200000 do add(F.int 0) done)));
  let z=Expr.Lit(Literal.Int(Z.shift_left Z.one 32768)) in
  reject(fun s -> P.emit_framed s "shared-Z"
    (F.list(fun add -> for _=1 to 40 do add(P.stream_expr z) done)))
let framing_individual_guards () =
  let reject f=let _,s,receipts,_=run_framed f in
    check "individual guard retained in v2" (s.P.failed<>None && not(complete receipts)) in
  reject(fun s -> P.emit_framed s "typed-depth"
    (P.stream_ast(List.init 4096(fun _ -> Asrt.Emp))));
  reject(fun _ ->
    let rec cyclic=0::cyclic in ignore(P.inspect_aggregate P.Expanded_parent cyclic));
  reject(fun _ -> ignore(P.inspect_aggregate P.Expanded_parent(fun x -> x)));
  reject(fun _ -> let z=Expr.Lit(Literal.Int(Z.shift_left Z.one 100)) in
    ignore(P.guarded_state ~projection:z ~assertions:(fun () -> [Asrt.Emp])
      ~to_json:(fun () -> failwith "must not convert unaccounted custom")));
  reject(fun s -> P.emit_framed s "integer-bit"
    (P.stream_expr(Expr.Lit(Literal.Int(Z.shift_left Z.one 65537)))))
let framing_physical_global_limits () =
  List.iter(fun mode ->
    let _,s,receipts,physical=run_framed
      ~record:(if mode="record" then 32 else P.max_record)
      ~bytes:(if mode="bytes" then 4096 else P.max_bytes)
      ~events:(if mode="events" then 2 else P.max_events)
      (fun s -> P.emit_framed s "fixture"(F.bytes(String.make 32768 'x'));
        P.finish ~procedure_tests:0 ~lemma_tests:0) in
    check (mode^" physical/commit/global cap fails closed")
      (s.P.failed<>None && not(complete receipts) &&
       List.for_all(fun r -> field "complete" r<>`Bool true)physical))
    ["record";"bytes";"events"];
  let _,s,receipts,_=run_framed ~bytes:4096(fun s ->
    s.P.bytes<-4096;P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "terminal exhaustion cannot produce complete receipt"
    (s.P.failed<>None && not(complete receipts))
let framing_default_passivity () =
  let _,s,_,physical=run(fun s -> P.emit s "fixture"(fun () -> `String "v1")) in
  check "default remains v1 physical record"
    (not s.P.framed && List.for_all(fun row ->
      field "format" row=`String "gillian-preparation-provenance-v1")physical);
  let carrier=ref 0 in
  let execute framed =
    let _,s,receipts=P.For_tests.run ~framed (fun _ -> ()) (fun s ->
      source s 1;group 0 [carrier];prepare carrier 1;
      P.finish ~procedure_tests:1 ~lemma_tests:0) in
    check "both profiles complete passive fixture" (s.P.failed=None && complete receipts);
    List.map(fun o -> o.P.raw_parent,o.alternative,o.expanded,o.states,o.tests)s.P.origins in
  check "capture profile retains lifecycle identity/order/counts"
    (execute false=execute true)


(* V3 controls belong to the same standalone executable. An optional bounded
   export writes EXACT sink bytes for the Python adoption controls; no Python
   framing substitute may satisfy their positive real-writer fixture. *)
let alternative_procedures = ["S05NormalizerPayloadCopy";"normalizeNode4"]
let alternative_lemmas = ["S05CompactAdvance";"S05CompactAppendOwned";"S05CompactExit";"S05CompactInit";"S05CompactOpen";"S05CompactTraceExtend";"S05CompactTraceRebase";"S05CopyAppendCell";"S05CopyBindCurrent";"S05CopyBoundedPrefixLength";"S05CopyConcatCut";"S05CopyCursorSplit";"S05CopyEqualCellKeys";"S05CopyIndexAdvance";"S05CopyIndexKeyRoundtrip";"S05CopyIndexPredecessor";"S05CopyInputCellsLength";"S05CopyIntegerPredecessor"]
let alternative_large = List.init 1500 (fun _ -> Asrt.Emp),None
let alternative_state = `Assoc ["raw",`String "\000\255";
  "duplicate",`Float 0.;"duplicate",`Float (-0.);
  "utf16-code-unit-bytes",`String "\216\000"]
let alternative_test_state = `String "test-distinct-\000\255"
let alternative_rank = Expr.Lit (Literal.Num (-0.))
let alternative_program ?(typed=false) () =
  let table () = Hashtbl.create 23 in
  let lemmas=table () and preds=table () in
  let three=Some (Expr.Lit (Literal.Int (Z.of_int 3))) in
  let seven=Some (Expr.Lit (Literal.Int (Z.of_int 7))) in
  if typed then Hashtbl.add preds "V3Typed" {Pred.pred_name="V3Typed";
    pred_source_path=None;pred_loc=None;pred_internal=true;pred_num_params=1;
    pred_params=["x",Some Type.NumberType];ins_number=1;
    pred_definitions=[None,[Asrt.Emp]];pred_facts=[];pred_guard=None;
    pred_pure=false;pred_abstract=false;pred_nounfold=false;pred_normalised=false};
  List.iter (fun name -> Hashtbl.add lemmas name {Lemma.lemma_name=name;
    lemma_source_path=None;lemma_internal=false;lemma_params=(if typed then ["p"] else []);
    lemma_specs=[{Lemma.lemma_hyp=pre;lemma_concs=[pre];
      lemma_spec_variant=(if typed then three else None)}];
    lemma_proof=Some [];lemma_variant=(if typed then seven else None);
    lemma_existentials=[];lemma_location=None}) alternative_lemmas;
  let procs=List.map (fun name ->
    let input=if typed && name="S05NormalizerPayloadCopy" then
      [Asrt.pred "V3Typed" [Expr.PVar "p"] []],None else pre in
    let count=if name="normalizeNode4" then 2 else 1 in
    let params=if typed then ["p"] else [] in
    let cases=List.init count (fun _ -> Spec.s_init input [pre] None Flag.Normal true) in
    {Proc.proc_name=name;proc_source_path=None;proc_internal=false;
     proc_body=[||];proc_params=params;
     proc_spec=Some (Spec.init name params cases false false true None);
     proc_aliases=[];proc_calls=[];proc_display_name=None;proc_hidden=false})
    alternative_procedures in
  Prog.make_indexed ~procs ~predecessors:[] ~lemmas ~preds ~funcs:(table ())
    ~datatypes:(table ()) ~only_specs:(table ()) ~macros:(table ()) ~bi_specs:(table ()) ()
let alternative_ordered s =
  List.concat_map (fun (kind,names) -> List.concat_map (fun name ->
    let src=match P.find_source s kind name with Some src -> src | None -> assert false in
    List.init (Array.length src.P.groups) (fun ordinal -> src,ordinal)) names)
    ["procedure",alternative_procedures;"lemma",alternative_lemmas]
let alternative_export ?(validate=(fun () -> ())) stem raw s observation =
  match Sys.getenv_opt "GILLIAN_PREPARATION_V3_FIXTURE_DIRECTORY" with
  | None -> validate ()
  | Some directory ->
      check "fixture export has canonical absolute directory"
        (not (Filename.is_relative directory) && Unix.realpath directory=directory);
      let save suffix text =
        let path=Filename.concat directory (stem^suffix) in
        let channel=open_out_gen [Open_wronly;Open_creat;Open_excl;Open_binary] 0o600 path in
        Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text) in
      save ".jsonl" raw;
      save ".stderr" (Printf.sprintf
        "PREPARATION_PROVENANCE path=%S session=%S complete=true reason=%S\n"
        s.P.path s.P.identity "closed-complete");
      (* Preserve exact sink bytes before any route shape assertion can fail.
         Shape observation flags are published only after validation succeeds. *)
      validate ();
      save "-observation.json" (Yojson.Safe.to_string (`Assoc (
        ["session",`String s.P.identity;"captured_path",`String s.P.path;
         "pid",`Int (Unix.getpid ());"proof_credit",`Bool false]@observation)) ^ "\n")
let alternative_fixture () =
  let raw = Buffer.create 16384 in
  let identity = Printf.sprintf "%d-%.6f" (Unix.getpid ()) (Unix.gettimeofday ()) in
  let path = "/test/v3/writer.jsonl" in
  let _,s,receipts = P.For_tests.run ~alternative:true ~path ~identity
    (Buffer.add_string raw) (fun s -> P.observe (fun _ ->
      let prog=alternative_program () in
      P.initialise s prog;
      P.before_expansion ~procs:prog.Prog.procs ~lemmas:prog.Prog.lemmas;
      let ordered=alternative_ordered s in
      let work = ref [] in
      List.iter (fun (src,ordinal) ->
        let large = src.P.name="S05NormalizerPayloadCopy" in
        let input = if large then alternative_large else pre in
        let count = if large then 30 else
          if src.P.name="normalizeNode4" && ordinal=0 then 0 else 1 in
        if src.P.kind="procedure" then (
          let cs=List.init count (fun _ -> Spec.s_init input [input] None Flag.Normal true) in
          P.spec_group src.P.name ordinal pre cs;
          List.iter (fun c -> work := (src.P.kind,src.P.name,Obj.repr c,input):: !work) cs)
        else (
          let cs=List.init count (fun _ -> {Lemma.lemma_hyp=input;
            lemma_concs=[input];lemma_spec_variant=None}) in
          P.lemma_group src.P.name ordinal pre cs;
          List.iter (fun c -> work := (src.P.kind,src.P.name,Obj.repr c,input):: !work) cs)) ordered;
      List.iteri (fun public (kind,name,carrier,input) ->
        let o=P.origin kind name (Obj.obj carrier) in
        let count=if public=0 then 2 else 1 in
        P.normalised o ~to_verify:true (fun () -> count) "ok";
        for native=0 to count-1 do
          P.snapshot o ~id:(public,native) ~phase:"normalized-state" (fun () ->
            `Assoc ["pre",P.located input;"state",alternative_state;
              "substitution",`List [`Tuple [`String "raw-key";`String "\000\255"]];
              "posts",P.posts [input]]);
          P.snapshot o ~id:(public,native) ~phase:"test-created" (fun () ->
            `Assoc ["state",alternative_test_state;"posts",P.posts [input];
              "verification_posts",P.posts [pre];"entry_rank",P.expr alternative_rank])
        done) (List.rev !work);
      P.finish ~procedure_tests:32 ~lemma_tests:18)) in
  Buffer.contents raw,s,receipts
let alternative_group_admission_and_export () =
  let cs=List.init 30 (fun _ -> Spec.s_init alternative_large [alternative_large] None Flag.Normal true) in
  let _,old,_,_=run_framed (fun s -> source s 1;
    P.spec_group "selected" 0 pre cs) in
  check "real old whole-group WORD cap rejects, not old occurrence cap"
    (old.P.failed=Some "aggregate:expanded-parent: value word budget");
  let raw,s,receipts=alternative_fixture () in
  check "same complete alternatives fit V3 fixture and all lifecycle totals close"
    (s.P.failed=None && complete receipts && List.length s.P.origins=49 &&
      List.fold_left (fun n o -> n+o.P.tests) 0 s.P.origins=50 && not s.P.group_open);
  let physical=String.split_on_char '\n' raw |> List.filter (fun x -> x<>"")
    |> List.map Yojson.Safe.from_string in
  let logical=logical_rows physical in
  let alternatives=List.filter (fun r -> field "event" r=`String "expanded-alternative" &&
    field "name" (data r)=`String "S05NormalizerPayloadCopy") logical in
  let expected=P.located alternative_large in
  check "all thirty ordered PRE/POST aliases survive real writer framing"
    (List.length alternatives=30 && (List.mapi (fun i r ->
      field "alternative" (data r)=`Int i && field "pre" (data r)=expected &&
      field "posts" (data r)=`List [expected]) alternatives |> List.for_all Fun.id));
  check "V3 physical/logical identifiers are distinct" (List.for_all (fun r ->
    field "format" r=`String "gillian-preparation-provenance-alternative-framed-v3") physical &&
    List.for_all (fun r -> field "format" r=`String "gillian-preparation-provenance-alternatives-v3") logical);
  alternative_export "writer-v3" raw s [
    "schema",`String "preparation-v3-writer-control-fixture-v1";
    "old_word_cap_rejected",`Bool true;"large_alternatives",`Int 30;
    "alias_occurrences_per_pre",`Int 1500;"raw_parents",`Int 21;
    "expanded",`Int 49;"total_tests",`Int 50]
(* Guard-only fixtures explicitly install their small known intermediate pins.
   They do not claim adoption of the real hook; the actual entrypoint fixture
   below is mandatory and independently observed by the Python controls. *)
let alternative_source s count =
  source s count;
  let src=match P.find_source s "procedure" "selected" with Some src -> src | None -> assert false in
  s.P.prepared_inputs<-List.init count (fun ordinal -> src,ordinal,Obj.repr pre);
  s.P.preparation_stage_started<-true;s.P.preparation_stage_complete<-true
let alternative_actual_preprocessing_entrypoint () =
  let module V=Utils.Config.Verification in
  let saved= !V.total,!V.things_to_verify,!V.things_to_exclude in
  Fun.protect ~finally:(fun () -> let total,selection,excluded=saved in
    V.total:=total;V.things_to_verify:=selection;V.things_to_exclude:=excluded)
    (fun () ->
    V.total:=true;V.things_to_verify:=V.All;V.things_to_exclude:=SS.empty;
    let raw=Buffer.create 16384 in
    let hook_closed=ref false and lemma_variants=ref true in
    let identity=Printf.sprintf "%d-%.6f" (Unix.getpid ()) (Unix.gettimeofday ()) in
    let _,s,receipts=P.For_tests.run ~alternative:true
      ~path:"/test/v3/route.jsonl" ~identity (Buffer.add_string raw) (fun s ->
      (* Actual entrypoint, not manual original/intermediate writer calls.
         The fixture has no commands, solver calls or proof execution. Typed
         predicate expansion and local admissibility use the real frontend. *)
      let result=Engine.LogicPreprocessing.preprocess (alternative_program ~typed:true ()) true in
      hook_closed := (s.P.failed=None && s.P.preparation_stage_complete &&
        List.length s.P.prepared_inputs=21 && List.length s.P.origins=21);
      List.iteri (fun public prior ->
        let input,posts,rank = if prior.P.source.kind="procedure" then
          let c : Spec.st=Obj.obj prior.P.carrier in c.ss_pre,c.ss_posts,c.ss_variant
        else let c : Lemma.spec=Obj.obj prior.P.carrier in
          lemma_variants := !lemma_variants &&
            c.lemma_spec_variant=Some(Expr.Lit(Literal.Int(Z.of_int 7)));
          c.lemma_hyp,c.lemma_concs,c.lemma_spec_variant in
        let o=P.origin prior.P.source.kind prior.P.source.name (Obj.obj prior.P.carrier) in
        P.normalised o ~to_verify:true (fun () -> 1) "ok";
        P.snapshot o ~id:(public,0) ~phase:"normalized-state" (fun () ->
          `Assoc ["pre",P.located input;"state",alternative_state;
            "substitution",`List [];"posts",P.posts posts]);
        P.snapshot o ~id:(public,0) ~phase:"test-created" (fun () ->
          `Assoc ["state",alternative_test_state;"posts",P.posts posts;
            "verification_posts",P.posts posts;"entry_rank",P.optional_expr rank]))
        (List.rev s.P.origins);
      P.finish ~procedure_tests:3 ~lemma_tests:18;
      result) in
    (* Receipt truth is checked before export; AST shape checks follow it. *)
    check "real preprocessing writer fixture closes all21 actual cases/tests"
      (s.P.failed=None && complete receipts);
    alternative_export ~validate:(fun () ->
    check "actual hook closed before frontend expansion completes" !hook_closed;
    check "actual unfolded lemma case takes declaration variant" !lemma_variants;
    let physical=String.split_on_char '\n' (Buffer.contents raw)
      |> List.filter (fun x -> x<>"") |> List.map Yojson.Safe.from_string in
    let logical=logical_rows physical in
    let parent event kind name =
      match List.find_opt (fun row -> field "event" row=`String event &&
        field "kind" (data row)=`String kind && field "name" (data row)=`String name &&
        field "raw_parent" (data row)=`Int 0) logical with
      | Some row -> data row | None -> failwith "missing actual route parent" in
    let original=parent "original-parent" "procedure" "S05NormalizerPayloadCopy" in
    let prepared=parent "pre-expansion-parent" "procedure" "S05NormalizerPayloadCopy" in
    let expanded=parent "expanded-alternative" "procedure" "S05NormalizerPayloadCopy" in
    let has_atom name located = match field "assertion" located with
      | `List xs -> List.exists (function `List (`String tag::_) -> tag=name | _ -> false) xs
      | _ -> false in
    let core_preds name located = match field "assertion" located with
      | `List xs -> List.filter (function
          | `List [`String "CorePred";`String actual;`List _;`List _] -> actual=name
          | _ -> false) xs
      | _ -> [] in
    let user=Asrt.user_pred_name "V3Typed" and domain="GILLIAN_INTERNAL_DEFINEDNESS" in
    let raw_pre=field "pre" original and prepared_pre=field "pre" prepared
      and expanded_pre=field "pre" expanded in
    check "raw procedure PRE precedes type elaboration" (not(has_atom "Types" raw_pre));
    check "raw procedure PRE retains named V3Typed user predicate" (core_preds user raw_pre<>[]);
    check "raw procedure PRE precedes internal domain preservation" (core_preds domain raw_pre=[]);
    check "intermediate procedure PRE differs from raw" (raw_pre<>prepared_pre);
    check "intermediate procedure PRE has elaborated Types" (has_atom "Types" prepared_pre);
    check "intermediate procedure PRE retains named V3Typed user predicate" (core_preds user prepared_pre<>[]);
    check "expanded procedure PRE removes only named V3Typed user predicate" (core_preds user expanded_pre=[]);
    let prepared_domains=core_preds domain prepared_pre
      and expanded_domains=core_preds domain expanded_pre in
    let genuine_domain = function
      | `List [`String "CorePred";`String name;
          `List [`List [`String "Lit";`List [`String "Bool";`Bool _]];_];`List []] -> name=domain
      | _ -> false in
    check "intermediate PRE retains genuine internal definedness obligations"
      (prepared_domains<>[] && List.for_all genuine_domain prepared_domains);
    check "expanded PRE retains genuine internal definedness obligations"
      (expanded_domains<>[] && List.for_all genuine_domain expanded_domains);
    (* Cartesian unfolding may reorder atoms and add definition obligations.
       Consume one structurally equal atom for each original occurrence. *)
    let rec remove_one wanted = function
      | [] -> None
      | x::xs -> if x=wanted then Some xs else
          Option.map (fun rest -> x::rest) (remove_one wanted xs) in
    let rec retained wanted actual = match wanted with
      | [] -> true
      | x::xs -> (match remove_one x actual with
          | None -> false | Some rest -> retained xs rest) in
    check "all intermediate domain occurrences retain expanded multiplicity"
      (retained prepared_domains expanded_domains);
    let name=List.hd alternative_lemmas in
    let original=parent "original-parent" "lemma" name in
    let prepared=parent "pre-expansion-parent" "lemma" name in
    let begin_=parent "expanded-parent-begin" "lemma" name in
    let binding=Asrt.Pure(Expr.BinOp(Expr.PVar "p",BinOp.ValueEqual,Expr.LVar "#p")) in
    let expected=match P.ast [binding] with `List [atom] -> atom | _ -> assert false in
    check "actual parameter-bound lemma differs from raw and anchors begin"
      (field "pre" original<>field "pre" prepared &&
       (match field "assertion" (field "pre" prepared) with
        | `List atoms -> List.mem expected atoms | _ -> false) &&
       field "input_pre" begin_=field "pre" prepared);
    let three=P.expr (Expr.Lit(Literal.Int(Z.of_int 3))) in
    let seven=P.expr (Expr.Lit(Literal.Int(Z.of_int 7))) in
    check "raw/intermediate per-case and declaration variants stay separate"
      (field "variant" original=three && field "variant" prepared=three &&
       field "declaration_variant" original=seven && field "declaration_variant" prepared=seven))
      "route-v3" (Buffer.contents raw) s [
      "schema",`String "preparation-v3-real-entrypoint-control-fixture-v1";
      "actual_preprocessing_entrypoint",`Bool true;"typed_procedure_observed",`Bool true;
      "parameter_bound_lemma_observed",`Bool true;"both_variant_sources_observed",`Bool true;
      "named_user_predicate_unfolded",`Bool true;"internal_definedness_preserved",`Bool true;
      "raw_parents",`Int 21;"expanded",`Int 21;"total_tests",`Int 21])
let alternative_atomic_failure_attribution () =
  let visited=ref [] in
  let expression=Expr.EList (List.init 1500 (fun _ -> Expr.BinOp(
    Expr.Lit Literal.Null,BinOp.ValueEqual,Expr.Lit Literal.Null))) in
  let oversized=List.init 17 (fun _ -> Asrt.Pure expression),None in
  let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
    alternative_source s 1;
    P.register_projected_group "procedure" "selected" 0 pre [ref 0;ref 1;ref 2]
      (fun c -> visited:= !c :: !visited;
        (if !c=1 then oversized else pre),[pre])) in
  check "failure stops at second alternative and never projects the third"
    (!visited=[1;0]);
  check "committed alternatives remain unpublished if parent end cannot commit"
    (s.P.origins=[] && s.P.group_open && not(complete receipts));
  check "bounded stopped failure identifies phase/parent/alternative"
    (match s.P.failed with Some why -> String.length why<512 &&
      String.starts_with ~prefix:"v3:group:procedure:" why &&
      (* Prefix contains both group and exact failed alternative context. *)
      (let needle="alternative=1: aggregate:expanded-parent: value word budget" in
       let rec contains i = i+String.length needle<=String.length why &&
         (String.sub why i (String.length needle)=needle || contains(i+1)) in contains 0)
      | None -> false)
let alternative_duplicate_carrier () =
  let c=Spec.s_init pre [pre] None Flag.Normal true in
  let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
    alternative_source s 1;P.spec_group "selected" 0 pre [c;c]) in
  check "V3 duplicate opaque carrier rejects without publishing staged origins"
    (s.P.origins=[] && not(complete receipts) && match s.P.failed with
     | Some why -> String.ends_with ~suffix:"ambiguous-physical-carrier" why
     | None -> false)
let alternative_shared_and_individual_guards () =
  let reject ?suffix f = let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ())
      (fun s -> P.observe (fun _ -> f s)) in
    check "V3 retained guard rejects with no complete receipt"
      (not(complete receipts) && match s.P.failed with
       | Some why -> (match suffix with None -> true | Some suffix -> String.ends_with ~suffix why)
       | None -> false) in
  let shared_reject input posts expected =
    let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
      (* These prerequisites are outside observe: failure is a failed control,
         not an apparently successful rejection by an earlier unrelated guard. *)
      P.typed_guard (fun v x -> v#visit_assertion () x) (fst input);
      ignore(P.inspect_aggregate P.Expanded_parent input);
      ignore(P.inspect_aggregate P.Posts posts);
      alternative_source s 1;P.spec_group "selected" 0 pre
        [Spec.s_init input posts None Flag.Normal true]) in
    check "individually legal PRE and entire POST list overflow their shared unit"
      (not(complete receipts) && match s.P.failed with
       | Some why -> String.ends_with ~suffix:("aggregate:expanded-parent: "^expected) why
       | None -> false) in
  let atom=Asrt.Pure(Expr.BinOp(Expr.PVar "a",BinOp.ValueEqual,Expr.PVar "b")) in
  let many=List.init 1500 (fun _ -> atom),None in
  shared_reject many (List.init 10 (fun _ -> many)) "value word budget";
  let text=Expr.PVar (String.make 60000 'x') in
  let one=[Asrt.Pure text],None in
  shared_reject one [one;one;one;one] "value string budget";
  reject (fun s -> P.emit_framed s "fixture"
    (F.list(fun add -> for _=1 to 200000 do add(F.int 0) done)));
  let z=Expr.Lit(Literal.Int(Z.shift_left Z.one 32768)) in
  reject (fun s -> P.emit_framed s "fixture"
    (F.list(fun add -> for _=1 to 40 do add(P.stream_expr z) done)));
  reject (fun s -> P.emit_framed s "fixture" (P.stream_expr
    (Expr.Lit (Literal.Int (Z.shift_left Z.one 65537)))));
  reject (fun s -> P.emit_framed s "fixture" (P.stream_ast
    (List.init 4096 (fun _ -> Asrt.Emp))));
  reject ~suffix:"aggregate:expanded-parent: cyclic capture fragment"
    (fun _ -> let rec cyclic=Asrt.Emp::cyclic in
    ignore(P.inspect_aggregate P.Expanded_parent cyclic));
  reject ~suffix:"aggregate:expanded-parent: unsupported host shape/closure"
    (fun _ -> ignore(P.inspect_aggregate P.Expanded_parent (fun x -> x)));
  let converted=ref false in
  reject ~suffix:"unaccounted-serialized-state-custom-block"
    (fun _ -> let z=Expr.Lit(Literal.Int(Z.shift_left Z.one 100)) in
    ignore(P.guarded_state ~projection:z ~assertions:(fun () -> [Asrt.Emp])
      ~to_json:(fun () -> converted:=true;`Null)));
  check "unaccounted state custom rejects before converter" (not !converted)

let alternative_closure_and_global_guards () =
  List.iter (fun mode ->
    let _,s,receipts=P.For_tests.run ~alternative:true
      ~events:(if mode="events" then 2 else P.max_events)
      ~bytes:(if mode="bytes" then 4096 else P.max_bytes)
      ~record:(if mode="record" then 32 else P.max_record)
      ~carriers:(if mode="carriers" then 0 else P.max_carriers)
      (fun _ -> ()) (fun s -> P.observe (fun _ -> alternative_source s 1;
        P.spec_group "selected" 0 pre [Spec.s_init pre [pre] None Flag.Normal true])) in
    check ("V3 fixed "^mode^" guard fails closed")
      (s.P.failed<>None && not(complete receipts))) ["events";"bytes";"record";"carriers"];
  let carriers=List.init 4097 (fun _ -> Spec.s_init pre [pre] None Flag.Normal true) in
  let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
    alternative_source s 1;P.spec_group "selected" 0 pre carriers) in
  check "actual4096 carrier cap is checked before begin/staging/projection"
    (s.P.events=1 && s.P.logical_events=0 && s.P.origins=[] && not s.P.group_open && not(complete receipts) &&
     match s.P.failed with Some why -> String.ends_with ~suffix:"expanded-carrier-cap" why
       | None -> false);
  let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
    alternative_source s 1;s.P.group_open<-true;P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "unfinished group prevents terminal complete" (s.P.failed<>None && not(complete receipts));
  let _,s,receipts=P.For_tests.run ~alternative:true ~bytes:4096 (fun _ -> ()) (fun s ->
    s.P.preparation_stage_complete<-true;s.P.bytes<-4096;P.finish ~procedure_tests:0 ~lemma_tests:0) in
  check "terminal reserve is unchanged" (s.P.failed<>None && not(complete receipts));
  let c=Spec.s_init pre [pre] None Flag.Normal true in
  let _,s,receipts=P.For_tests.run ~alternative:true (fun _ -> ()) (fun s ->
    alternative_source s 2;P.spec_group "selected" 0 pre [c];ignore(P.origin "procedure" "selected" c)) in
  check "no normalization consumes origins until ALL groups close"
    (s.P.failed=Some "origin-before-group-closure" && not(complete receipts))


(* V4 controls append to the exact historical33. These are future controls,
   never ordinary proof/normalization semantics or original-case evidence. *)
module X = Engine.Preparation_snapshot
let v4_snapshots s = match s.P.snapshot with Some d->X.completed d|None->assert false
let v4_export ~validate stem raw s observations =
  check "v4 export requires a closed complete actual writer receipt"
    (s.P.closed && s.P.failed=None && s.P.terminal);
  let save directory suffix text =
    let path=Filename.concat directory(stem^suffix)in
    let channel=open_out_gen[Open_wronly;Open_creat;Open_excl;Open_binary]0o600 path in
    Fun.protect ~finally:(fun()->close_out channel)(fun()->output_string channel text);
    Unix.chmod path 0o444 in
  match Sys.getenv_opt "GILLIAN_PREPARATION_V4_FIXTURE_DIR"with
  | None->validate()
  | Some directory->
    check "v4 fixture export directory is absolute and canonical"
      (not(Filename.is_relative directory)&&Unix.realpath directory=directory);
    save directory ".jsonl" raw;
    save directory ".stderr"(Printf.sprintf
      "PREPARATION_PROVENANCE path=%S session=%S complete=true reason=%S\n"
      s.P.path s.P.identity "closed-complete");
    (* Exact raw+receipt precede shape assertions; flags never survive a failed
       assertion as a positive expected observation file. *)
    validate();
    save directory ".expected.json"(Yojson.Safe.to_string(`Assoc(
      ["schema",`String"preparation-v4-real-writer-fixture-v1";
       "session",`String s.P.identity;"captured_path",`String s.P.path;
       "pid",`Int(Unix.getpid());"proof_credit",`Bool false;
       "raw_parents",`Int 21;"expanded",`Int 21;"total_tests",`Int 21;
       "snapshots",`List(v4_snapshots s)]@observations))^"\n")
let v4_sha_vectors () =
  check "SHA256 empty known vector"
    (X.For_tests.sha256 ""="e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
  check "SHA256 abc known vector"
    (X.For_tests.sha256 "abc"="ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
  check "SHA256 multi-block known vector"
    (X.For_tests.sha256 "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"=
      "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")
let v4_scalar_and_meter_fidelity () =
  let cases=[`Null;`Bool true;`Int(-7);`Float 0.;`Float(-0.);`String"\000\255\216\000";
    `Intlit"0000123";`Variant("v\000",None);`Variant("v",Some(`Tuple[`Null;`Int 1]));
    `List[];`Tuple[];`Assoc[];`Assoc["duplicate",`Float 0.;"duplicate",`Float(-0.)]]in
  List.iter(fun value->
    let buffer=Buffer.create 128 and meter=F.create(fun _->())in
    F.json value meter;F.json value(F.create(Buffer.add_string buffer));
    let shape=X.For_tests.shape value in
    check "v4 structural words/strings equal unchanged old streaming meter"
      (match shape with rw::tw::rs::ts::_->
        [rw;tw;rs;ts]=[meter.F.raw.words;meter.F.tagged.words;meter.F.raw.strings;meter.F.tagged.strings]
       |_->false);
    check "control oracle preserves exact old tagged bytes"
      (Buffer.contents buffer=Yojson.Safe.to_string(C.tag value)))cases
let v4_state changed =
  let rows=List.init 31(fun row->`Assoc(List.init 1000(fun i->
    (if i=0 then "a" else if i=1 then "b" else "k"),
    (if changed&&row=30&&i=999 then `Bool true else `Null))))in
  `Assoc["state",`Assoc["heap",`List rows;
    "store",`List[`Tuple[`String"alias";`Float 0.];`Tuple[`String"alias";`Float(-0.)]];
    "pfs",`List[`String"first\000\255";`String"middle";`String"first\000\255"];
    "gamma",`Assoc[];"spec_vars",`List[]];"preds",`List[];"wands",`List[]]
let v4_guard_state value = P.guarded_state ~projection:value
  ~assertions:(fun()->[Asrt.Emp]) ~to_json:(fun()->value)
let v4_small_state = `Assoc["state",`Assoc["heap",`List[];"store",`List[];
  "pfs",`List[];"gamma",`Assoc[];"spec_vars",`List[]];"preds",`List[];"wands",`List[]]
let v4_old_words_reject payload =
  try F.json payload(F.create(fun _->()));false
  with C.Incomplete why->why="v2-transport-word-cap"
let v4_large_export () =
  let large=v4_state false and changed=v4_state true in
  (* Guard prerequisites are OUTSIDE capture/observe. A different earlier
     failure can never impersonate the intended whole-old-unit rejection. *)
  ignore(v4_guard_state large);ignore(v4_guard_state changed);
  let posts=[alternative_large;alternative_large;alternative_large]in
  let normalized=`Assoc["pre",P.located alternative_large;"state",large;
    "substitution",`List[];"posts",P.posts posts]in
  let test=`Assoc["state",changed;"posts",P.posts posts;
    "verification_posts",P.posts posts;"entry_rank",P.optional_expr(Some alternative_rank)]in
  check "genuine large state exceeds64 immediate entries and keeps first/last/repeated PFS"
    (match field"heap"(field"state"large),field"pfs"(field"state"large)with
      |`List((`Assoc entries)::_),`List[first;_;last]->List.length entries=1000&&first=last
      |_->false);
  let raw=Buffer.create 16384 in
  let identity=Printf.sprintf "%d-%.6f"(Unix.getpid())(Unix.gettimeofday())in
  let _,s,receipts=P.For_tests.run ~field_framed:true
    ~path:"/test/v4/large.jsonl"~identity(Buffer.add_string raw)(fun s->P.observe(fun _->
    let prog=alternative_program()in P.initialise s prog;
    P.before_expansion ~procs:prog.Prog.procs ~lemmas:prog.Prog.lemmas;
    let work=ref[]in
    List.iter(fun(src,ordinal)->
      let big=src.P.name="S05NormalizerPayloadCopy"in
      let input=if big then alternative_large else pre in
      let posts=if big then posts else[pre]in
      if src.P.kind="procedure"then(
        let c=Spec.s_init input posts None Flag.Normal true in
        P.spec_group src.P.name ordinal pre[c];
        work:=(src.P.kind,src.P.name,Obj.repr c,input,posts,big):: !work)
      else(let c={Lemma.lemma_hyp=input;lemma_concs=posts;lemma_spec_variant=None}in
        P.lemma_group src.P.name ordinal pre[c];
        work:=(src.P.kind,src.P.name,Obj.repr c,input,posts,big):: !work))
      (alternative_ordered s);
    List.iteri(fun public(kind,name,carrier,input,posts,big)->
      let origin=P.origin kind name(Obj.obj carrier)in
      P.normalised origin ~to_verify:true(fun()->1)"ok";
      P.snapshot_fields origin ~id:(public,0)~phase:"normalized-state"~prepare:(fun()->())
        ["pre",(fun()->P.located input);
         "state",(fun()->v4_guard_state(if big then large else v4_small_state));
         "substitution",(fun()->`List[]);"posts",(fun()->P.posts posts)];
      P.snapshot_fields origin ~id:(public,0)~phase:"test-created"~prepare:(fun()->())
        ["state",(fun()->v4_guard_state(if big then changed else v4_small_state));
         "posts",(fun()->P.posts posts);"verification_posts",(fun()->P.posts posts);
         "entry_rank",(fun()->P.optional_expr(Some alternative_rank))]) (List.rev !work);
    P.finish ~procedure_tests:3 ~lemma_tests:18))in
  check "v4 actual large writer completes21parents21tests without weakening state guards"
    (s.P.failed=None&&complete receipts&&List.length(v4_snapshots s)=42);
  v4_export ~validate:(fun()->
    check "both full normalized and test OLD word units actually reject"
      (v4_old_words_reject normalized&&v4_old_words_reject test);
    let large_rows=List.filter(fun row->match field"origin"row with
      |`List[_;`String"S05NormalizerPayloadCopy";_;_;_]->true|_->false)(v4_snapshots s)in
    check "large exported usage exceeds old tagged whole-snapshot cap in BOTH phases"
      (List.length large_rows=2&&List.for_all(fun row->match field"usage"row with
        |`List(_::`Int tw::_)->tw>1048576|_->false)large_rows))
    "snapshot-large-v4"(Buffer.contents raw)s
    ["large",`Bool true;"guarded_large_state",`Bool true;"nested_state_runs",`Bool true;
     "old_normalized_word_cap_rejected",`Bool true;"old_test_word_cap_rejected",`Bool true]

(* Genuine ordinary generic-state backend for the ACTUAL preprocessing and
   Verifier test-construction route. Its empty heap has no primitive actions;
   any unexpected memory operation fails rather than fabricating a result. *)
module V4Memory=struct
  include Engine.SMemory.Dummy
  let mem_constraints _=[]
  let get_print_info variables _=variables,SS.empty
  let substitution_in_place ~pfs:_ ~gamma:_ _ heap=[heap,Expr.Set.empty,[]]
  let assertions ?to_keep:_ _=[]
  let lvars _=SS.empty
  let alocs _=SS.empty
  let clean_up ?keep:_ _=Expr.Set.empty,Expr.Set.empty
  let sure_is_nonempty _=false
end
module V4State=Engine.SState.Make(V4Memory)
module V4PState=Engine.PState.Make(V4State)
module V4Verifier=Engine.Verifier.Make(V4State)(V4PState)(ParserAndCompiler.Dummy)
  (Engine.External.Dummy(ParserAndCompiler.Dummy.Annot))
let v4_route_program () =
  let prog=alternative_program ~typed:true()in
  let target=Expr.EList[Expr.Lit(Literal.Loc"$v4-global");Expr.LVar"#v4_scope_witness"]in
  Hashtbl.add prog.Prog.preds "V4KeepScope"{Pred.pred_name="V4KeepScope";
    pred_source_path=None;pred_loc=None;pred_internal=true;pred_num_params=1;
    pred_params=["scope",None];ins_number=1;pred_definitions=[];pred_facts=[];
    pred_guard=None;pred_pure=false;pred_abstract=true;pred_nounfold=true;pred_normalised=false};
  Hashtbl.iter(fun name (proc:(_,_)Proc.t)->
    let spec=Option.get proc.proc_spec in
    let scoped=name="S05NormalizerPayloadCopy"in
    let params=if scoped then proc.proc_params@["x__v4_scope"]else proc.proc_params in
    let cases=List.map(fun(c:Spec.st)->
      {c with ss_variant=Some(Expr.Lit(Literal.Int(Z.of_int 7)));
        ss_posts=(if scoped then[([Asrt.pred"V4KeepScope"[target][]],None)]else c.ss_posts);
        ss_verifier_scope=(if scoped then Some{Spec.vsb_source=Expr.PVar"x__v4_scope";
          vsb_target=target}else None)})spec.spec_sspecs in
    Hashtbl.replace prog.procs name{proc with proc_params=params;
      proc_spec=Some{spec with spec_params=params;spec_sspecs=cases}})prog.procs;prog
let rec v4_contains wanted json = json=wanted||match json with
  |`List xs|`Tuple xs->List.exists(v4_contains wanted)xs
  |`Assoc xs->List.exists(fun(_,x)->v4_contains wanted x)xs
  |`Variant(_,Some x)->v4_contains wanted x
  |_->false
let v4_route_export () =
  check "standalone controls explicitly disabled eager SMT startup"
    (Sys.getenv_opt "GILLIAN_PREPARATION_CONTROLS_NO_SOLVER" = Some "1");
  check "solver access from startup remains fail-closed before any real route"
    (try ignore (Smt.exec_sat Expr.Set.empty (Hashtbl.create 0)); false with
     | Smt.SMT_error message -> message = "SMT solver is terminally shut down");
  let module V=Utils.Config.Verification in
  let saved= !V.total,!V.things_to_verify,!V.things_to_exclude in
  Fun.protect ~finally:(fun()->let total,selection,excluded=saved in
    V.total:=total;V.things_to_verify:=selection;V.things_to_exclude:=excluded)(fun()->
    V.total:=true;V.things_to_verify:=V.All;V.things_to_exclude:=SS.empty;
    (* No control may silently start SMT. The pure empty-heap route must use
       the existing simplifier's definite empty-formula fast path. *)
    Smt.shutdown_solver();
    let actual=ref[]in
    let observe ~phase ~kind ~name ~parent ~alternative ~expanded ~native ~role value =
      actual:=((phase,kind,name,parent,alternative,expanded,native,role),value):: !actual in
    let raw=Buffer.create 16384 in
    let identity=Printf.sprintf "%d-%.6f"(Unix.getpid())(Unix.gettimeofday())in
    let _,s,receipts=X.For_tests.with_field_observer observe(fun()->
      P.For_tests.run ~field_framed:true ~path:"/test/v4/route.jsonl"~identity
        (Buffer.add_string raw)(fun s->
        let prog=Engine.LogicPreprocessing.preprocess(v4_route_program())true in
        check "actual preprocessing hook closed exact21 current-table parents"
          (s.P.failed=None&&s.P.preparation_stage_complete&&List.length s.P.prepared_inputs=21&&List.length s.P.origins=21);
        let procedures,lemmas=V4Verifier.Debug.prepare_tests_for_prog ~init_data:() prog in
        check "actual Verifier constructs all3procedure18lemma tests without BODY"
          (procedures=3&&lemmas=18)))in
    check "actual route complete receipt precedes raw export"
      (s.P.failed=None&&complete receipts&&List.length(v4_snapshots s)=42);
    let get phase kind name parent role =
      match List.find_opt(fun((p,k,n,r,_,_,_,f),_)->p=phase&&k=kind&&n=name&&r=parent&&f=role)!actual with
      |Some(_,value)->value|None->failwith"missing actual v4 field observation"in
    let normalized kind name parent role=get"normalized-state"kind name parent role in
    let test kind name parent role=get"test-created"kind name parent role in
    let source_field_matches row role value =
      field role (field "field_sha256" row)=
        `String(X.For_tests.sha256(Yojson.Safe.to_string(C.tag value))) in
    v4_export ~validate:(fun()->
      let caller="S05NormalizerPayloadCopy"and lemma=List.hd alternative_lemmas in
      let prepared=List.find(fun(src,_,_)->src.P.kind="procedure"&&src.P.name=caller)s.P.prepared_inputs in
      let _,_,prepared=prepared in
      let input:Asrt.t Utils.Location.located=Obj.obj prepared in
      check "real type-elaborated procedure PRE is observed"
        (List.exists(function Asrt.Types _->true|_->false)(fst input));
      let lemma_pre=normalized"lemma"lemma 0"pre"in
      check "actual lemma parameter binding survives into normalized source PRE"
        (v4_contains(P.expr(Expr.PVar"p"))lemma_pre);
      (* Parameter bindings may be lifted solely into a lemma's store. The
         typed caller's real Types normalization instead exports PVar p in
         the actual unfiltered substitution, before Verifier's later filter. *)
      let p_key=P.expr(Expr.PVar"p")in
      let caller_substitution=normalized"procedure"caller 0"substitution"in
      let bindings=match caller_substitution with
        |`List bindings->bindings
        |_->failwith"actual extended substitution is not a binding list"in
      let p_bindings=List.filter_map(function
        |`List[key;value]when key=p_key->Some value|_->None)bindings in
      check "actual typed caller substitution has one PVar p key and fresh LVar value"
        (match p_bindings with
         |[`List[`String"LVar";`String name]]->
             String.starts_with ~prefix:Utils.Names.lvar_prefix name
         |_->false);
      let p_value=match p_bindings with[value]->value|_->assert false in
      let caller_store=field"store"(field"state"(normalized"procedure"caller 0"state"))in
      check "actual caller substitution agrees with its normalized program store"
        (match caller_store with
         |`List entries->List.exists(function
             |`List[`String"p";value]->value=p_value|_->false)entries
         |_->false);
      let caller_row=List.find(fun row->
        field"phase"row=`String"normalized-state"&&
        match field"origin"row with
        |`List[`String"procedure";`String name;`Int 0;_;_]->name=caller
        |_->false)(v4_snapshots s)in
      let without_p=`List(List.filter(function
        |`List[key;_]->key<>p_key|_->true)bindings)in
      let altered_p=`List(List.map(function
        |`List[key;`List[`String"LVar";`String name]]when key=p_key->
            `List[key;P.expr(Expr.LVar(name^"__changed"))]
        |binding->binding)bindings)in
      (* One full-field oracle serves the actual positive, both genuine
         binding counterfactuals, and every callback field below. A no-op or
         always-true oracle fails the negatives; always-false fails positive. *)
      check "source-field oracle accepts the actual complete caller substitution"
        (source_field_matches caller_row "substitution" caller_substitution);
      check "same source-field oracle rejects deletion of the actual p binding"
        (not(source_field_matches caller_row "substitution" without_p));
      check "same source-field oracle rejects alteration of the actual p value"
        (not(source_field_matches caller_row "substitution" altered_p));
      let normal_state=normalized"lemma"lemma 0"state"and test_state=test"lemma"lemma 0"state"in
      check "actual lemma store is legitimately cleared only for test state"
        (field"store"(field"state"normal_state)<>Engine.SStore.to_yojson(Engine.SStore.init[])&&
         field"store"(field"state"test_state)=Engine.SStore.to_yojson(Engine.SStore.init[])&&normal_state<>test_state);
      check "public and verification-only test POSTs remain distinct"
        (test"procedure"caller 0"posts"<>test"procedure"caller 0"verification_posts");
      check "actual evaluated entry rank is captured, not raw case/declaration fiction"
        (test"procedure"caller 0"entry_rank"=P.expr(Expr.Lit(Literal.Int(Z.of_int 7))));
      check "equal procedure and legitimately changed lemma states are BOTH observed"
        (normalized"procedure""normalizeNode4"0"state"=test"procedure""normalizeNode4"0"state"&&normal_state<>test_state);
      (* Independent small actual-value oracle observes ALL8 real callback
         fields and checks their canonical bytes against the committed result. *)
      List.iter(fun row->
        let phase=match field"phase"row with `String x->x|_->assert false in
        let kind,name,parent=match field"origin"row with
          |`List[`String k;`String n;`Int p;_;_]->k,n,p|_->assert false in
        match field"field_sha256"row with
        |`Assoc hashes->List.iter(fun(role,_)->
          let actual=get phase kind name parent role in
          check "all actual callback fields equal exact old tagged canonical digest"
            (source_field_matches row role actual))hashes
        |_->assert false)(v4_snapshots s))
      "snapshot-route-v4"(Buffer.contents raw)s
      (List.map(fun name->name,`Bool true)
        ["actual_preprocessing_entrypoint";"actual_test_construction_entrypoint";
         "typed_procedure_observed";"parameter_bound_lemma_observed";
         "unfiltered_substitution_observed";"legitimate_lemma_store_change_observed";
         "public_verification_posts_distinct_observed";"evaluated_rank_observed";
         "equal_and_changed_states_observed"]))
let v4_guard_and_atomic_closure () =
  let reject ~suffix f =
    let _,s,receipts=P.For_tests.run ~field_framed:true(fun _->())(fun s->
      P.observe(fun _->f s))in
    check "v4 failed construction never publishes complete receipt"
      (not(complete receipts)&&v4_snapshots s=[]&&match s.P.failed with
       |Some why->String.ends_with ~suffix why|None->false)in
  reject ~suffix:"control-stopped-state"(fun s->alternative_source s 1;
    let c=Spec.s_init pre[pre]None Flag.Normal true in P.spec_group"selected"0 pre[c];
    let origin=P.origin"procedure""selected"c in
    P.normalised origin ~to_verify:true(fun()->1)"ok";
    P.snapshot_fields origin ~id:(0,0)~phase:"normalized-state"~prepare:(fun()->())
      ["pre",(fun()->P.located pre);"state",(fun()->raise(C.Incomplete"control-stopped-state"));
       "substitution",(fun()->`List[]);"posts",(fun()->P.posts[pre])]);
  reject ~suffix:"v4-import-value-drift"(fun s->alternative_source s 1;
    let c=Spec.s_init pre[pre]None Flag.Normal true in P.spec_group"selected"0 pre[c];
    let origin=P.origin"procedure""selected"c in
    P.normalised origin ~to_verify:true(fun()->1)"ok";
    P.snapshot_fields origin ~id:(0,0)~phase:"normalized-state"~prepare:(fun()->())
      ["pre",(fun()->P.located([Asrt.Pure(Expr.Lit Literal.Null)],None));
       "state",(fun()->v4_small_state);"substitution",(fun()->`List[]);"posts",(fun()->P.posts[pre])]);
  reject ~suffix:"record-integer-conversion-cap"(fun s->alternative_source s 1;
    let c=Spec.s_init pre[pre]None Flag.Normal true in P.spec_group"selected"0 pre[c];
    let origin=P.origin"procedure""selected"c in
    P.normalised origin ~to_verify:true(fun()->1)"ok";
    P.snapshot_fields origin ~id:(0,0)~phase:"normalized-state"
      ~prepare:(fun()->for _=1 to 15 do P.charge_integer 65536 done)
      ["pre",(fun()->P.located pre);
       "state",(fun()->P.charge_integer 65536;v4_small_state);
       "substitution",(fun()->P.charge_integer 1;`List[]);
       "posts",(fun()->P.posts[pre])]);
  let text=String.make 60000 'x'in
  let posts=List.init 4(fun _->[Asrt.Pure(Expr.PVar text)],None)in
  let state=`Assoc["state",`Assoc["heap",`List(List.init 4(fun _->`String text));
    "store",`List[];"pfs",`List[];"gamma",`Assoc[];"spec_vars",`List[]];
    "preds",`List[];"wands",`List[]]in
  (* Individually legal source fields; their combined old-data tagged strings
     exceed the unchanged shared1MiB total. No per-field reset may admit them. *)
  ignore(v4_guard_state state);
  ignore(P.inspect_aggregate P.Expanded_parent(pre,posts));
  ignore(P.posts posts);ignore(P.expr(Expr.PVar text));
  reject ~suffix:"v4-expanded-snapshot-strings"(fun s->alternative_source s 1;
    let c=Spec.s_init pre posts None Flag.Normal true in P.spec_group"selected"0 pre[c];
    let origin=P.origin"procedure""selected"c in
    P.normalised origin ~to_verify:true(fun()->1)"ok";
    P.snapshot_fields origin ~id:(0,0)~phase:"normalized-state"~prepare:(fun()->())
      ["pre",(fun()->P.located pre);"state",(fun()->v4_guard_state state);
       "substitution",(fun()->P.expr(Expr.PVar text));"posts",(fun()->P.posts posts)]);
  let converted=ref false in
  let z=Expr.Lit(Literal.Int(Z.shift_left Z.one 100))in
  (try ignore(P.guarded_state ~projection:z ~assertions:(fun()->[Asrt.Emp])
    ~to_json:(fun()->converted:=true;`Null));failwith"missing unknown custom rejection"
   with C.Incomplete why->check "v4 keeps exact serialized custom admission"
     (why="unaccounted-serialized-state-custom-block"&&not !converted))

let () = Alcotest.run "Preparation provenance (standalone)"
  ["capture",List.map (fun (name,f) -> Alcotest.test_case name `Quick f)
    ["disabled",disabled;"exact parent mapping and lemma ids",exact_mapping;
     "zero normalized",zero_normalized;"unverified",unverified;
     "duplicate carrier",duplicate_carrier;"coverage and totals",missing_and_totals;
     "fixed limits",limits;"serializer and IO",serializer_and_io;
     "stale output",stale_output;"state custom guard",state_custom_guard;
     "output parent scope",output_parent_scope;
     "aggregate integer conversion budget",integer_conversion_budget;
     "selector",selection;
     "aggregate flat containers",aggregate_flat_containers;
     "aggregate combined and alias limits",aggregate_combined_alias_limits;
     "aggregate cycles and host shapes",aggregate_cycles_and_host_shapes;
     "unchanged AST and transport guards",unchanged_ast_and_transport_guards;
     "expanded payload ownership",expanded_payload_ownership;
     "expanded whole event budget",expanded_whole_event_budget;
     "expanded empty and carrier admission",expanded_empty_and_carrier_admission];
   "framed v2",List.map(fun(name,f) -> Alcotest.test_case name `Quick f)
     ["exact existing grammar",framing_exact_grammar;
      "exact host word meter",framing_exact_word_meter;
      "large repeated lifecycle",framing_large_multiplicity;
      "shared logical budgets",framing_shared_limits;
      "individual guards",framing_individual_guards;
      "physical/global/terminal budgets",framing_physical_global_limits;
      "default and lifecycle passivity",framing_default_passivity];
   "alternative framed v3",List.map(fun(name,f) -> Alcotest.test_case name `Quick f)
     ["whole group word change and real writer export",alternative_group_admission_and_export;
      "actual preprocessing boundary and full source variants",alternative_actual_preprocessing_entrypoint;
      "atomic publication and stopped attribution",alternative_atomic_failure_attribution;
      "duplicate opaque carrier",alternative_duplicate_carrier;
      "combined alternative and individual guards",alternative_shared_and_individual_guards;
      "group closure and unchanged global guards",alternative_closure_and_global_guards];
   "field framed v4",List.map(fun(name,f)->Alcotest.test_case name `Quick f)
     ["SHA256 known vectors",v4_sha_vectors;
      "exact scalar grammar and old meters",v4_scalar_and_meter_fidelity;
      "guarded large normalized and test writer export",v4_large_export;
      "atomic field closure and retained guards",v4_guard_and_atomic_closure;
      "actual preprocessing and test construction writer export",v4_route_export]]
