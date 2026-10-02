open Gillian.Gil_syntax
module Preds = Engine.Preds
module SI = Utils.Containers.SI

let consume ?(maintain = false) predicates name args ins =
  Preds.consume_pred ~maintain predicates name args (SI.of_list ins) Expr.equal

let expect label expected actual =
  Alcotest.(check bool) label true (expected = actual)

let nullary () =
  let predicates = Preds.init [ ("Context", []); ("Other", []) ] in
  expect "consume the owned nullary predicate" (Some ("Context", []))
    (consume predicates "Context" [] []);
  expect "preserve the unrelated resource" [ ("Other", []) ]
    (Preds.to_list predicates);
  expect "consumed ownership cannot be reused" None
    (consume predicates "Context" [] [])

let output_only () =
  let value = Expr.int 7 in
  let predicates = Preds.init [ ("Witness", [ value ]) ] in
  expect "learn an unknown output with no inputs" (Some ("Witness", [ value ]))
    (consume predicates "Witness" [ None ] []);
  expect "consume the output-bearing resource" [] (Preds.to_list predicates)

let maintain () =
  let predicates = Preds.init [ ("Context", []); ("Context", []) ] in
  expect "maintain returns the existing assertion" (Some ("Context", []))
    (consume ~maintain:true predicates "Context" [] []);
  Alcotest.(check int) "maintain does not remove either copy" 2
    (Preds.length predicates);
  ignore (consume predicates "Context" [] []);
  Alcotest.(check int) "ordinary matching consumes exactly one copy" 1
    (Preds.length predicates)

let missing_and_wrong_input () =
  let predicates = Preds.init [ ("Other", []); ("Owned", [ Expr.int 3 ]) ] in
  let before = Preds.to_list predicates in
  expect "missing name cannot invent ownership" None
    (consume predicates "Context" [] []);
  expect "wrong input cannot match" None
    (consume predicates "Owned" [ Some (Expr.int 4) ] [ 0 ]);
  expect "rejections preserve all resources" before (Preds.to_list predicates)

let reject_inputs_before_outputs () =
  let output = Expr.LVar "#unrelated_output" in
  let predicates = Preds.init [ ("Segment", [ Expr.int 1; output ]) ] in
  let before = Preds.to_list predicates and output_queries = ref 0 in
  let eq left right =
    if Expr.equal left output then incr output_queries;
    Expr.equal left right
  in
  expect "mismatched inputs still reject" None
    (Preds.consume_pred ~maintain:false predicates "Segment"
       [ Some (Expr.int 2); Some (Expr.LVar "#wanted_output") ]
       (SI.singleton 0) eq);
  Alcotest.(check int) "no output query after input rejection" 0 !output_queries;
  expect "input rejection preserves resources" before (Preds.to_list predicates)

let semantic_output_ranking () =
  let input = Expr.int 1 and output = Expr.int 7 in
  let alias = Expr.LVar "#alias" in
  let predicates = Preds.init
      [ ("Segment", [ input; Expr.int 3 ]); ("Segment", [ input; output ]) ] in
  let eq left right = Expr.equal left right ||
    (Expr.equal left output && Expr.equal right alias) in
  expect "matching inputs retain semantic output preference"
    (Some ("Segment", [ input; output ]))
    (Preds.consume_pred ~maintain:false predicates "Segment"
       [ Some input; Some alias ] (SI.singleton 0) eq);
  expect "unselected output resource remains"
    [ ("Segment", [ input; Expr.int 3 ]) ] (Preds.to_list predicates)

let semantic_input_and_output_only () =
  let input = Expr.int 1 and alias = Expr.LVar "#alias" in
  let eq left right = Expr.equal left right ||
    (Expr.equal left input && Expr.equal right alias) in
  let predicates = Preds.init [ ("Input", [ input ]); ("Output", [ input ]) ] in
  expect "semantic input matching is retained" (Some ("Input", [ input ]))
    (Preds.consume_pred ~maintain:false predicates "Input" [ Some alias ]
       (SI.singleton 0) eq);
  expect "known output with no inputs is checked semantically"
    (Some ("Output", [ input ]))
    (Preds.consume_pred ~maintain:false predicates "Output" [ Some alias ]
       SI.empty eq);
  expect "both exclusive resources were consumed" [] (Preds.to_list predicates)

let reject_remaining_inputs () =
  let wrong_object = Expr.ALoc "wrong" and wanted_object = Expr.ALoc "wanted" in
  let wrong_length = Expr.LVar "#unrelated_length" in
  let length_alias = Expr.LVar "#length_alias" and wanted_length = Expr.int 7 in
  let output = Expr.LVar "#output" in
  let wrong = ("Segment", [ wrong_object; wrong_length; output ]) in
  let right = ("Segment", [ wanted_object; wanted_length; output ]) in
  let predicates = Preds.init [ wrong; right ] in
  let unrelated_queries = ref 0 and semantic_queries = ref 0 in
  let eq left right =
    if Expr.equal left wrong_length then (
      incr unrelated_queries;
      failwith "unrelated length must not be queried")
    else if Expr.equal left wanted_length && Expr.equal right length_alias then (
      incr semantic_queries;
      true)
    else Expr.equal left right
  in
  let args = [ Some wanted_object; Some length_alias; None ] in
  expect "select the owned object with a semantic length match" (Some right)
    (Preds.consume_pred ~maintain:false predicates "Segment" args
       (SI.of_list [ 0; 1 ]) eq);
  Alcotest.(check int) "no remaining input query after object mismatch" 0
    !unrelated_queries;
  Alcotest.(check int) "a later input of a viable candidate is checked" 1
    !semantic_queries;
  expect "wrong-object ownership remains" [ wrong ] (Preds.to_list predicates);
  expect "wrong object cannot supply the requested ownership" None
    (Preds.consume_pred ~maintain:false predicates "Segment" args
       (SI.of_list [ 0; 1 ]) eq);
  Alcotest.(check int) "rejection still avoids unrelated length queries" 0
    !unrelated_queries;
  expect "failed consumption preserves ownership" [ wrong ]
    (Preds.to_list predicates)

let insertion_length_dependencies () =
  let module MP = Gillian.Abstraction.MP in
  let keys = Expr.LVar "#keys" and position = Expr.LVar "#position" in
  let key = Expr.LVar "#key" and result = Expr.LVar "#result" in
  let length = Expr.UnOp (LstLen, Expr.NOp (LstInsert, [ keys; position; key ])) in
  let known = Expr.Set.of_list [ keys; position; key ] in
  let equality = Asrt.Pure (Expr.BinOp (result, Equal, length)) in
  let plan known = MP.s_init_atoms ~preds:(Hashtbl.create 0)
      (Expr.Set.add result known) [ equality ] in
  Alcotest.(check bool) "known insertion operands no longer crash planning" true
    (Result.is_ok (plan known));
  List.iter
    (fun operand ->
      Alcotest.(check bool) "every insertion operand is required" false
        (Result.is_ok (plan (Expr.Set.remove operand known))))
    [ keys; position; key ];
  let length_only = Expr.Set.add (Expr.UnOp (LstLen, keys))
      (Expr.Set.remove keys known) in
  Alcotest.(check bool) "list length alone cannot supply the inserted list" false
    (Result.is_ok (plan length_only));
  expect "result length cannot invent insertion witnesses" []
    (MP.learn_expr (Expr.Set.singleton result) result length);
  match plan known with
  | Ok [ (_, outs) ] -> expect "equality invents no insertion outputs" [] outs
  | _ -> Alcotest.fail "expected one complete equality matching step"

(* Exercise real post production, including its final store update. No heap
   operation is needed for this return/predicate binding regression. *)
module ReturnState = Engine.SState.Make (Engine.SMemory.Dummy)
module ReturnMatcher = Engine.Matcher.Make (ReturnState)
module ReturnSubst = Engine.SVal.SESubst
module ReturnStore = Engine.SStore

let return_var = Expr.PVar Utils.Names.return_variable
let returned state = ReturnStore.get (ReturnState.get_store state.ReturnMatcher.state)
    Utils.Names.return_variable |> Option.get

let return_state () : ReturnMatcher.t =
  let pred : Pred.t = {
    pred_name = "ReturnValue"; pred_source_path = None; pred_loc = None;
    pred_internal = false; pred_num_params = 1; pred_params = ["value", None];
    ins_number = 1; pred_definitions = []; pred_facts = []; pred_guard = None;
    pred_pure = true; pred_abstract = true; pred_nounfold = true;
    pred_normalised = true;
  } in
  let pred_defs = Engine.MP.init_pred_defs () in
  Hashtbl.add pred_defs pred.pred_name Engine.MP.{
    pred; def_mp = Finished None; guard_mp = None };
  { state = ReturnState.init (); preds = Preds.init []; wands = Engine.Wands.init [];
    pred_defs }

let with_total_return f () =
  let old = !Utils.Config.Verification.total in
  Utils.Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Utils.Config.Verification.total := old) f

let return_post op value = [
  Asrt.Pure (Expr.BinOp (return_var, op, value));
  Asrt.pred "ReturnValue" [return_var] [] ]

let check_return_pred state =
  match Preds.to_list state.ReturnMatcher.preds with
  | [("ReturnValue", [value])] ->
      Alcotest.(check bool) "later predicate and final store share the return witness"
        true (ReturnState.equals state.state value (returned state))
  | _ -> Alcotest.fail "expected one return predicate"

let exact_return_posts () =
  let values = [Expr.num 0.; Expr.num (-0.); Expr.num nan;
    Expr.Lit (Literal.Bool false); Expr.Lit Literal.Null;
    Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical (Utils.Utf16.of_code_units [0xd800])));
    Expr.LVar "#returned_object"; Expr.EList [Expr.num (-0.); Expr.Lit Literal.Null];
    Expr.LVar "#returned_value"] in
  List.iter (fun value ->
    let bindings = match value with
      | Expr.LVar _ -> [value, value]
      | _ -> [] in
    let initial = return_state () and subst = ReturnSubst.init bindings in
    if Expr.equal value (Expr.LVar "#returned_object") then
      ignore (ReturnState.assume_t initial.state value Type.ObjectType);
    let results = ReturnMatcher.produce_posts initial subst [return_post ValueEqual value] in
    match results with
    | [state] ->
        Alcotest.(check bool)
          "value identity survives a later predicate and final store copy"
          true (ReturnState.equals state.state value (returned state));
        check_return_pred state;
        expect "the caller substitution remains untouched" None
          (ReturnSubst.get subst return_var);
        expect "the caller store remains untouched" None
          (ReturnStore.get (ReturnState.get_store initial.state) Utils.Names.return_variable)
    | _ -> Alcotest.fail "expected one exact return state") values

let numeric_return_posts () =
  let initial = return_state () in
  match ReturnMatcher.produce_posts initial (ReturnSubst.init [])
    [return_post Equal (Expr.num 0.)] with
  | [state] ->
      check_return_pred state;
      let ret = returned state in
      let opposite = Expr.BinOp (ret, ValueEqual, Expr.num (-0.)) in
      Alcotest.(check bool) "ordinary zero equality still permits negative zero" true
        (ReturnState.sat_check state.state opposite);
      Alcotest.(check bool) "ordinary zero equality still permits positive zero" true
        (ReturnState.sat_check state.state (Expr.BinOp (ret, ValueEqual, Expr.num 0.)));
      Alcotest.(check bool) "ordinary zero equality cannot invent a nonzero return" false
        (ReturnState.sat_check state.state (Expr.BinOp (ret, ValueEqual, Expr.num 1.)))
  | _ -> Alcotest.fail "expected one numeric equality state"

let nan_return_posts () =
  let initial = return_state () and subst = ReturnSubst.init [] in
  expect "ordinary NaN equality has no feasible return" []
    (ReturnMatcher.produce_posts initial subst [return_post Equal (Expr.num nan)]);
  expect "failed production cannot bind the caller return" None
    (ReturnSubst.get subst return_var)

let existing_return_posts () =
  let value = Expr.Lit (Literal.Bool true) in
  let initial = return_state () and subst = ReturnSubst.init [return_var, value] in
  match ReturnMatcher.produce_posts initial subst [return_post ValueEqual value] with
  | [state] ->
      expect "an existing return binding remains authoritative" value (returned state);
      check_return_pred state;
      expect "existing caller substitution is preserved" (Some value)
        (ReturnSubst.get subst return_var)
  | _ -> Alcotest.fail "expected one existing return state"

let alternative_return_posts () =
  let initial = return_state () and subst = ReturnSubst.init [] in
  let values = [Expr.Lit (Literal.Bool true); Expr.Lit (Literal.Bool false)] in
  let results = ReturnMatcher.produce_posts initial subst
    (List.map (return_post ValueEqual) values) in
  expect "post alternatives retain independent exact values" values
    (List.map returned results);
  List.iter check_return_pred results;
  expect "alternative bindings do not escape to the caller" None
    (ReturnSubst.get subst return_var)

(* Two automatic unfolds must accumulate their recovered facts. The second
   retry cannot return to a snapshot that has consumed the first predicate
   without retaining its produced resource. Exercise the real matcher. *)
module RecoveryState = Engine.SState.Make (struct
  include Engine.SMemory.Dummy
  (* This fixture has no heap cells. Pure substitutions preserve its empty heap. *)
  let substitution_in_place ~pfs:_ ~gamma:_ _ heap =
    [(heap, Expr.Set.empty, [])]
end)
module RecoveryMatcher = Engine.Matcher.Make (RecoveryState)

let recovery_state () =
  let x = Expr.LVar "#recovery_x" and y = Expr.LVar "#recovery_y" in
  let initial : RecoveryMatcher.t = {
    state = RecoveryState.add_spec_vars (RecoveryState.init ())
      (Utils.Containers.SS.of_list ["#recovery_x"; "#recovery_y"]);
    preds = Preds.init []; wands = Engine.Wands.init [];
    pred_defs = (return_state ()).pred_defs;
  } in
  let definition name value =
    let pred : Pred.t = {
      pred_name = name; pred_source_path = None; pred_loc = None;
      pred_internal = false; pred_num_params = 1; pred_params = ["value", None];
      ins_number = 1;
      pred_definitions = [None, [Asrt.Pure
        (Expr.BinOp (Expr.PVar "value", Equal, Expr.int value))]];
      pred_facts = []; pred_guard = None; pred_pure = false;
      pred_abstract = false; pred_nounfold = false; pred_normalised = true;
    } in
    Hashtbl.add initial.pred_defs name Engine.MP.{
      pred; def_mp = Finished None; guard_mp = None }
  in
  definition "FirstRecovery" 1;
  definition "SecondRecovery" 2;
  ignore (RecoveryState.assume_t initial.state x Type.IntType);
  ignore (RecoveryState.assume_t initial.state y Type.IntType);
  Preds.extend ~pure:false initial.preds ("FirstRecovery", [x]);
  Preds.extend ~pure:false initial.preds ("SecondRecovery", [y]);
  Preds.extend ~pure:true initial.preds ("ReturnValue", [Expr.LVar "#recovery_frame"]);
  (initial, x, y)

let recovery_match initial x y second =
  let steps = List.map (fun (variable, value) ->
    (Asrt.Pure (Expr.BinOp (variable, Equal, Expr.int value)), []))
    [x, 1; y, second] in
  RecoveryMatcher.match_ initial (ReturnSubst.init [x, x; y, y])
    (Engine.MP.of_step_list steps) Engine.Matcher.LogicCommand

let sequential_recovery () =
  let initial, x, y = recovery_state () in
  let before = Preds.to_list initial.preds in
  match recovery_match initial x y 2 with
  | [Ok (state, _, _)] ->
      Alcotest.(check bool) "first recovered fact survives the second retry" true
        (RecoveryState.equals state.state x (Expr.int 1));
      Alcotest.(check bool) "second recovered fact is established" true
        (RecoveryState.equals state.state y (Expr.int 2));
      expect "unrelated frame remains owned" [("ReturnValue", [Expr.LVar "#recovery_frame"])]
        (Preds.to_list state.preds);
      expect "recovery does not consume the caller snapshot" before
        (Preds.to_list initial.preds)
  | results ->
      let errors = List.filter_map (function Error err -> Some err | Ok _ -> None) results in
      Alcotest.fail (Fmt.str "expected a complete match after two recovery steps: %a"
        Fmt.(Dump.list RecoveryState.pp_err_t) errors)

let false_recovery_goal () =
  let initial, x, y = recovery_state () in
  let before = Preds.to_list initial.preds in
  let results = recovery_match initial x y 3 in
  Alcotest.(check bool) "recovery cannot invent a false second fact" false
    (List.exists Result.is_ok results);
  expect "rejected recovery preserves the caller snapshot" before
    (Preds.to_list initial.preds)

let tests =
  List.map (fun (name, test) -> Alcotest.test_case name `Quick test)
    [
      ("reject remaining inputs", reject_remaining_inputs);
      ("reject inputs before outputs", reject_inputs_before_outputs);
      ("semantic output ranking", semantic_output_ranking);
      ("semantic input and output-only matching", semantic_input_and_output_only);
      ("nullary ownership", nullary);
      ("output-only witness", output_only);
      ("maintain and multiplicity", maintain);
      ("missing name and mismatched input", missing_and_wrong_input);
      ("insertion length dependencies", insertion_length_dependencies);
      ("exact summary return", with_total_return exact_return_posts);
      ("numeric summary return", with_total_return numeric_return_posts);
      ("infeasible NaN summary return", with_total_return nan_return_posts);
      ("existing summary return", with_total_return existing_return_posts);
      ("alternative summary returns", with_total_return alternative_return_posts);
      ("sequential recovery preserves frame", with_total_return sequential_recovery);
      ("false sequential recovery rejects", with_total_return false_recovery_goal);
    ]
