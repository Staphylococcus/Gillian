open Gillian.Gil_syntax
module C = Utils.Owned_prefix_lifecycle
module P = Predicate_matching
module M = P.RecoveryMatcher
module S = P.RecoveryState
let check message value = Alcotest.(check bool) message true value
let root state f = C.with_root ~target:"S05CompactAppendOwned" ~case_id:(0,0) ~state f
let run ?enabled ?bytes ?events ?event_bytes f =
  let lines = ref [] in
  let old = !Utils.Config.dump_smt in
  if enabled <> Some false then Utils.Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Utils.Config.dump_smt:=old) (fun () ->
    let value,available = C.For_tests.run ?enabled ?bytes ?events ?event_bytes
      (fun line -> lines := Yojson.Safe.from_string line :: !lines) f in
    value,available,List.rev !lines)
let field key = function
  | `Assoc fields -> Option.value ~default:`Null (List.assoc_opt key fields)
  | _ -> `Null
let has event lines = List.exists (fun row -> field "event" row = `String event) lines
let tuple = [Expr.LVar "#a";Expr.num 0.;Expr.num (-0.);
  Expr.EList [Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical
    (Utils.Utf16.of_code_units [0xd800])))];Expr.ESet []]
let fixture ?(copies=1) () : M.t =
  let pred = { (P.call_mode_pred ~abstract:true 3) with
    pred_name="S05StringCells";pred_num_params=5;
    pred_params=List.map (fun name -> name,None) ["a";"start";"end";"values";"keys"] } in
  let defs=Engine.MP.init_pred_defs () in
  Hashtbl.add defs pred.pred_name Engine.MP.{pred;def_mp=Finished None;guard_mp=None};
  {state=S.init ();preds=Engine.Preds.init (List.init copies (fun _ -> pred.pred_name,tuple));
   wands=Engine.Wands.init [];pred_defs=defs}
let consume state args = M.consume_pred ~no_auto_fold:true state "S05StringCells" args
let disabled () =
  let state=fixture () and called=ref false in
  let _,ok,lines=run ~enabled:false (fun () -> root state (fun () ->
    C.event "never" ~state (fun () -> called:=true;failwith "disabled payload");
    ignore (consume state (List.map Option.some tuple)))) in
  check "disabled callback is inert and emits no IO" (ok && not !called && lines=[]);
  check "disabled actual consume still removes one resource" (Engine.Preds.length state.preds=0)
let direct () =
  let state=fixture ~copies:2 () in
  let before=Engine.Preds.to_list state.preds in
  let result,ok,lines=run (fun () -> root state (fun () -> consume state (List.map Option.some tuple))) in
  check "real direct consume succeeds" (match result with [Ok _] -> true | _ -> false);
  check "exactly one duplicate is consumed" (Engine.Preds.to_list state.preds=[List.hd before]);
  check "both actual direct lifecycle boundaries emitted" (ok && has "direct-consume-before" lines && has "direct-consume-after" lines);
  check "raw tuple including zero signs/surrogate is captured" (List.exists (fun row ->
    field "tuples" (field "data" row)=`List [
      `List [`String "S05StringCells";`List (List.map Expr.to_yojson tuple)];
      `List [`String "S05StringCells";`List (List.map Expr.to_yojson tuple)]]) lines)
let missing () =
  List.iter (fun args -> let state=fixture () in
    let before=Engine.Preds.to_list state.preds in
    let result,ok,lines=run (fun () -> root state (fun () -> consume state args)) in
    check "input mismatch rejects without inventing ownership" (List.for_all Result.is_error result);
    check "all failed resources remain" (before=Engine.Preds.to_list state.preds);
    check "miss is recorded" (ok && has "direct-consume-after" lines))
    [Some (Expr.LVar "#other")::List.tl (List.map Option.some tuple)];
  let state=fixture ~copies:0 () in
  let result,ok,_=run (fun () -> root state (fun () -> consume state (List.map Option.some tuple))) in
  check "absent resource remains a failure" (ok && List.for_all Result.is_error result)
let production () =
  let state=fixture ~copies:0 () in
  let alias=Expr.PVar "captured_end" in
  let subst=P.ReturnSubst.init [List.nth tuple 0,List.nth tuple 0;
    alias,List.nth tuple 2] in
  let post=[Asrt.pred "S05StringCells" [List.nth tuple 0;Expr.num 0.;alias]
    (List.filteri (fun i _ -> i>=3) tuple)] in
  let before=P.ReturnSubst.to_yojson subst in
  let results,ok,lines=run (fun () -> root state (fun () -> M.produce_posts state subst [post])) in
  check "real post produces exact raw full tuple" (match results with [s] ->
    Engine.Preds.to_list s.M.preds=["S05StringCells",tuple] | _ -> false);
  check "observer leaves caller ownership and substitution unchanged"
    (Engine.Preds.to_list state.preds=[] && before=P.ReturnSubst.to_yojson subst);
  check "actual post producer captured" (ok && has "predicate-produced" lines)
let opacity () =
  let pred={ (P.call_mode_pred ~abstract:false 1) with
    pred_name="S05StringCells";pred_num_params=1;pred_params=["value",None];
    pred_nounfold=true;pred_definitions=[None,[Asrt.Pure
      (Expr.BinOp (Expr.PVar "value",Equal,Expr.int 1))]] } in
  let x=P.unfold_summary_output in
  let initial=P.unfold_summary_state pred [x] in
  let before=Engine.Preds.to_list initial.preds in
  let low,ok,lines=run (fun () -> root initial (fun () ->
    M.unfold_with_vals ~auto_level:`Low initial [x])) in
  check "Low preserves opaque resource" (ok && low=None && before=Engine.Preds.to_list initial.preds);
  check "Low selection was observed" (has "selection-after" lines);
  let goal=Engine.MP.of_step_list [Asrt.Pure (Expr.BinOp (x,Equal,Expr.int 1)),[]] in
  P.recovery_attempts:=0;
  let result,ok,lines=run (fun () -> root initial (fun () ->
    M.match_ initial (P.ReturnSubst.init [x,x]) goal Engine.Matcher.LogicCommand)) in
  let recovered=match result with [Ok (state,_,_)] -> state
    | _ -> Alcotest.fail "real failed match must recover" in
  check "failed matcher invoked actual recovery" (ok && !(P.recovery_attempts)>0);
  check "recovered fact is actually established" (S.equals recovered.state x (Expr.int 1));
  check "real recovered frame and original ownership are preserved"
    (Engine.Preds.to_list recovered.preds=[P.unfold_summary_frame] &&
     Engine.Preds.to_list initial.preds=before);
  let find event rows=List.find (fun row -> field "event" row=`String event) rows in
  let top=find "match-enter" lines and recovery=find "recovery-enter" lines in
  let high=List.find (fun row -> field "event" row=`String "selection-after" &&
    field "level" (field "details" (field "data" row))=`String "High") lines in
  let branch=find "unfold-alternative-enter" lines in
  check "recovery scope is an actual child of the failed match"
    (field "parent_scope" recovery=field "scope" top);
  check "High selection joins recovery scope and state"
    (field "scope" high=field "scope" recovery &&
     field "state" high=field "scope_entry_state" recovery &&
     field "scope_entry_state" high=field "scope_entry_state" recovery);
  let selected=`List [`String "S05StringCells";`List [Expr.to_yojson x]] in
  check "High selects the exact owned opaque tuple"
    (field "selected" (field "details" (field "data" high))=selected);
  check "selected linear tuple is removed before unfolding"
    (field "tuples" (field "data" high)=`List []);
  check "actual alternative has recovery parent and the selected predicate"
    (field "parent_scope" branch=field "scope" recovery &&
     field "predicate" (field "data" branch)=`String "S05StringCells");
  List.iter (fun row ->
    check "actual recovery scope/state IDs are present"
      (match field "state" row,field "scope_entry_state" row with
       | `Int a,`Int b -> a>0 && b>0 | _ -> false)) [top;recovery;high;branch];
  List.iter (fun row -> if field "event" row=`String "native-query" then
    check "any actual recovery query joins a recorded scope/state"
      (field "query" (field "data" row)<>`String "none" &&
       List.exists (fun entry ->
         (match field "event" entry with
          | `String name -> String.ends_with ~suffix:"-enter" name
          | _ -> false) &&
         field "scope" entry=field "scope" row &&
         field "scope_entry_state" entry=field "scope_entry_state" row) lines)) lines;
  let rejected=P.unfold_summary_state pred [x] in
  let before=Engine.Preds.to_list rejected.preds in
  let bad=Engine.MP.of_step_list [Asrt.Pure (Expr.BinOp (x,Equal,Expr.int 2)),[]] in
  let result,ok,_=run (fun () -> root rejected (fun () ->
    M.match_ rejected (P.ReturnSubst.init [x,x]) bad Engine.Matcher.LogicCommand)) in
  check "real recovery cannot invent the false requested fact"
    (ok && not (List.exists Result.is_ok result) && before=Engine.Preds.to_list rejected.preds)
let scopes () =
  let make () =
    let state=fixture () in
    let vars=List.map (fun name -> Expr.PVar name) ["a";"count";"prefix";"keys"] in
    let a=List.nth vars 0 and count=List.nth vars 1 in
    let prefix=List.nth vars 2 and keys=List.nth vars 3 in
    let atom=Asrt.pred "S05StringCells" [a;Expr.num 0.;count] [prefix;keys] in
    let steps=match Engine.MP.s_init_atoms ~preds:(Hashtbl.create 0)
        (Expr.Set.of_list [a;count]) [atom] with
      | Ok xs -> xs | Error _ -> Alcotest.fail "actual owned-prefix body plan" in
    let pred={ (P.call_mode_pred ~abstract:false 2) with
      pred_name="S05CompactOwnedPrefix";pred_num_params=4;
      pred_params=List.map (fun name -> name,None) ["a";"count";"prefix";"keys"] } in
    let definition=Engine.MP.{pred;def_mp=of_step_list steps;guard_mp=None} in
    Hashtbl.add state.pred_defs pred.pred_name definition;state,definition
  in
  let expected=[List.nth tuple 0;List.nth tuple 2;List.nth tuple 3;List.nth tuple 4] in
  let explicit,definition=make () in
  let result,ok,explicit_lines=run (fun () -> root explicit (fun () ->
    M.fold ~match_kind:Engine.Matcher.LogicCommand ~state:explicit
      definition [List.nth tuple 0;List.nth tuple 2])) in
  check "real explicit fold owns exactly the produced full wrapper"
    (ok && match result with [Ok s] ->
      Engine.Preds.to_list s.M.preds=["S05CompactOwnedPrefix",expected] | _ -> false);
  let find event rows=List.find (fun row -> field "event" row=`String event) rows in
  let explicit_fold=find "fold-enter" explicit_lines in
  check "explicit fold retains LogicCommand kind"
    (field "kind" (field "data" explicit_fold)=Engine.Matcher.match_kind_to_yojson Engine.Matcher.LogicCommand);
  let missing,_=make () in
  check "POST fixture has no wrapper, only its underlying full cells"
    (Engine.Preds.to_list missing.preds=["S05StringCells",tuple]);
  let post=Asrt.pred "S05CompactOwnedPrefix" [List.nth tuple 0;List.nth tuple 2]
    [List.nth tuple 3;List.nth tuple 4] in
  let steps=match Engine.MP.s_init_atoms ~preds:(Hashtbl.create 0)
      (Expr.Set.singleton (List.nth tuple 0)) [post] with
    | Ok xs -> xs | Error _ -> Alcotest.fail "real missing-wrapper POST plan" in
  let post_kind=Engine.Matcher.Postcondition "S05CompactAppendOwned" in
  let result,ok,lines=run (fun () -> root missing (fun () ->
    M.match_ missing (P.ReturnSubst.init [List.nth tuple 0,List.nth tuple 0])
      (Engine.MP.of_step_list steps) post_kind)) in
  check "real POST auto-fold consumes cells and newly produced wrapper"
    (ok && match result with [Ok (s,_,_)] -> Engine.Preds.to_list s.M.preds=[] | _ -> false);
  let top=find "match-enter" lines and fold=find "fold-enter" lines in
  let assertion=List.find (fun row -> field "event" row=`String "assertion-enter" &&
    field "scope" row=field "parent_scope" fold) lines in
  let nested=List.find (fun row -> field "event" row=`String "match-enter" &&
    field "parent_scope" row=field "scope" fold) lines in
  let actual_fold_kind=Engine.Matcher.Fold "S05CompactOwnedPrefix" in
  check "POST ancestry is preserved while actual child kind remains Fold pname"
    (field "kind" (field "data" top)=Engine.Matcher.match_kind_to_yojson post_kind &&
     field "parent_scope" assertion=field "scope" top &&
     field "kind" (field "data" fold)=Engine.Matcher.match_kind_to_yojson actual_fold_kind &&
     field "kind" (field "data" nested)=Engine.Matcher.match_kind_to_yojson actual_fold_kind);
  let selected=`List [`String "S05CompactOwnedPrefix";`List (List.map Expr.to_yojson expected)] in
  let owned_results=List.filter (fun row -> field "event" row=`String "direct-consume-after" &&
    field "name" (field "details" (field "data" row))=`String "S05CompactOwnedPrefix") lines in
  check "POST genuinely misses wrapper then consumes the exact reconstructed tuple"
    (match owned_results with [miss;hit] ->
      field "selected" (field "details" (field "data" miss))=`Null &&
      field "selected" (field "details" (field "data" hit))=selected &&
      field "scope" miss=field "scope" assertion && field "scope" hit=field "scope" assertion
     | _ -> false);
  List.iter (fun row -> check "POST fold scope/state joins are present"
    (field "root" row=field "root" top && match field "state" row,field "scope_entry_state" row with
      | `Int a,`Int b -> a>0 && b>0 | _ -> false)) [top;assertion;fold;nested]
let query_join () =
  let state=fixture () in
  let old= !Utils.Config.dump_smt in Utils.Config.dump_smt:=true;
  Fun.protect ~finally:(fun () -> Utils.Config.dump_smt:=old) (fun () ->
    let result,ok,lines=run (fun () -> root state (fun () ->
      let fs=Expr.Set.singleton Expr.false_ and gamma=Hashtbl.create 0 in
      let before=Expr.Set.elements fs in
      let result=Smt.exec_sat ~caller_kind:"lifecycle-control" fs gamma in
      check "original FS and Gamma remain exact" (before=Expr.Set.elements fs && Hashtbl.length gamma=0);
      result)) in
    check "real complete native contradiction remains UNSAT" (result=None);
    check "actual allocated native query joins active scope" (ok && has "native-query" lines &&
      List.exists (fun row -> field "event" row=`String "native-query" &&
        field "query" (field "data" row)<>`String "none") lines))
let unavailable () =
  let state=fixture () in
  List.iter (fun f -> let initial=fixture () in
    let _,ok,lines=run (fun () -> root initial (fun () -> f ();
      ignore (consume initial (List.map Option.some tuple)))) in
    check "diagnostic failure cannot change actual resource consumption" (Engine.Preds.length initial.preds=0);
    check "failure explicitly makes diagnosis unavailable" (not ok && has "unavailable" lines))
    [(fun () -> C.event "bad" ~state (fun () -> failwith "snapshot"));
     (fun () -> C.query ~query:"none" ~caller:"control");
     (fun () -> C.event "oversized" ~state (fun () -> `String (String.make 8192 'x')))];
  let _,ok,lines=run ~events:4 (fun () -> root state (fun () ->
    for _=1 to 5 do C.event "bounded" ~state (fun () -> `Null) done)) in
  check "cap never presents truncated tuple as complete" (not ok && List.length lines<=4 && has "unavailable" lines);
  let _,ok,lines=run ~bytes:512 (fun () -> root state (fun () ->
    for _=1 to 5 do C.event "bytes" ~state (fun () -> `String (String.make 128 'x')) done)) in
  check "byte cap is explicit" (not ok && has "unavailable" lines);
  let _,ok=C.For_tests.run (fun _ -> failwith "sink") (fun () -> root state (fun () ->
    ignore (consume state (List.map Option.some tuple)))) in
  check "IO failure cannot suppress the original consume" (not ok && Engine.Preds.length state.preds=0)
let tests = List.map (fun (name,f) ->
  Alcotest.test_case name `Quick (P.with_total_return f)) [
  "disabled actual path",disabled;"direct one-resource consume",direct;
  "input mismatch and missing resource",missing;"read-only post production",production;
  "High Low nounfold",opacity;"command POST scopes",scopes;
  "real native query join",query_join;"caps and serialization unavailable",unavailable]
