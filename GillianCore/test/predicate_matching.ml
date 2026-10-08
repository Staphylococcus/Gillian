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
module RecoveryStateBase = Engine.SState.Make (struct
  include Engine.SMemory.Dummy
  (* This fixture has no heap cells. Pure substitutions preserve its empty heap. *)
  let substitution_in_place ~pfs:_ ~gamma:_ _ heap =
    [(heap, Expr.Set.empty, [])]
end)
let recovery_attempts = ref 0
module RecoveryState = struct
  include RecoveryStateBase
  let get_recovery_tactic state errors =
    incr recovery_attempts;
    RecoveryStateBase.get_recovery_tactic state errors
end
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

let refuted_recovery_goal () =
  let initial, x, y = recovery_state () in
  let facts = [Expr.BinOp (x, Equal, Expr.int 1);
               Expr.BinOp (y, Equal, Expr.int 2)] in
  let state = Option.get (RecoveryState.assume_a initial.state facts) in
  let initial = {initial with state} in
  let before = Preds.to_list initial.preds in
  recovery_attempts := 0;
  let results = recovery_match initial x y 3 in
  Alcotest.(check bool) "state-proved false goal is rejected" false
    (List.exists Result.is_ok results);
  Alcotest.(check int) "known false goal performs no predicate recovery" 0
    !recovery_attempts;
  expect "refuted goal preserves owned predicates" before
    (Preds.to_list initial.preds)

let conjunctive_location_identity () =
  let module Reduction = Gillian.Logic.Reduction in
  let module Gamma = Gillian.Symbolic.Type_env in
  let x = Expr.LVar "#location_x" and y = Expr.LVar "#location_y" in
  let location = Expr.ALoc "#loc_closure_environment" in
  let gamma = Gamma.init () in
  List.iter (fun name -> Gamma.update gamma name Type.ObjectType)
    ["#location_x"; "#location_y"];
  let eq a b = Expr.BinOp (a, Equal, b) in
  let conjunction = Expr.BinOp (eq y x, And, eq x location) in
  let pfs = Engine.PFS.of_list [conjunction] in
  let before = Engine.PFS.to_list pfs in
  expect "nested aliases resolve to the actual environment"
    (Some "#loc_closure_environment")
    (Reduction.resolve_expr_to_location pfs gamma y);
  expect "location lookup preserves the original facts" before
    (Engine.PFS.to_list pfs);
  List.iter (fun (label, fact) ->
    expect label None
      (Reduction.resolve_expr_to_location (Engine.PFS.of_list [fact]) gamma x))
    [ ("disjunction does not establish an identity",
        Expr.BinOp (eq x location, Or, eq x (Expr.ALoc "#loc_other")));
      ("negation does not establish an identity", Expr.UnOp (Not, eq x location));
      ("implication does not establish an identity",
        Expr.BinOp (Expr.LVar "#condition", Impl, eq x location)) ]

(* Generated list-pattern witnesses must reject an inapplicable alternative,
   not read past the supplied list or feed an unsubstituted formal to SMT. *)
let list_witness_case actual wanted =
  let initial : RecoveryMatcher.t = {
    state = RecoveryState.init ();
    preds = Preds.init [("CallerFrame", [])];
    wands = Engine.Wands.init [];
    pred_defs = Engine.MP.init_pred_defs ();
  } in
  let tree = Expr.PVar "tree" in
  let elements = List.init wanted (fun i -> Expr.LVar ("#element_" ^ string_of_int i)) in
  let outs = List.mapi (fun i variable ->
    variable, Expr.BinOp (tree, LstNth, Expr.int i)) elements in
  let step = Asrt.Pure (Expr.BinOp (tree, Equal, Expr.EList elements)), outs in
  let supplied = Expr.EList (List.init actual (fun i -> Expr.int (i + 1))) in
  let subst = ReturnSubst.init [tree, supplied] in
  let before = Preds.to_list initial.preds in
  let results = RecoveryMatcher.match_ initial (ReturnSubst.copy subst)
    (Engine.MP.of_step_list [step]) Engine.Matcher.LogicCommand in
  expect "matching keeps the caller frame snapshot" before (Preds.to_list initial.preds);
  expect "matching keeps the caller substitution" (Some supplied) (ReturnSubst.get subst tree);
  List.iter (fun element ->
    expect "proposed outputs do not leak to the caller" None (ReturnSubst.get subst element)) elements;
  if actual = wanted then (
    match results with
    | [Ok (state, learned, _)] ->
        expect "successful match preserves the frame" before (Preds.to_list state.preds);
        List.iteri (fun i element ->
          expect "only actual list values are learned" (Some (Expr.int (i + 1)))
            (ReturnSubst.get learned element)) elements
    | _ -> Alcotest.fail "expected the applicable list alternative to match")
  else
    Alcotest.(check bool) "wrong list shape cannot manufacture a witness" false
      (List.exists Result.is_ok results)

let applicable_list_witnesses () =
  list_witness_case 0 0;
  list_witness_case 2 2;
  list_witness_case 3 3

let partial_list_witnesses () =
  list_witness_case 0 1;
  list_witness_case 2 3

let wrong_list_shape () =
  list_witness_case 3 2

let source_precondition_guard () =
  let env = Expr.LVar "#source_env" in
  let normalised_loc = Expr.ALoc "normalised_env" in
  let global = Expr.Lit (Literal.Loc "$lg") in
  let guard = Asrt.Pure (Expr.UnOp (Not, Expr.BinOp (env, Equal, global))) in
  let original = [guard; Asrt.Types [env, Type.ObjectType]] in
  let normalised = [Asrt.Pure (Expr.BinOp (env, Equal, normalised_loc))] in
  let exported = Engine.MP.retain_precondition_guards ~original ~bindings:[] normalised in
  let plan assertion =
    match Engine.MP.init (Expr.Set.of_list [env; normalised_loc])
        Expr.Set.empty (Hashtbl.create 0) [assertion, (None, None)] with
    | Ok mp -> mp
    | Error _ -> Alcotest.fail "source guards must remain plannable"
  in
  let matches assertion actual =
    ReturnMatcher.match_ (return_state ())
      (ReturnSubst.init [env, actual; normalised_loc, actual])
      (plan assertion) Engine.Matcher.LogicCommand
    |> List.exists Result.is_ok
  in
  Alcotest.(check bool) "normalized location alone admits the global alias" true
    (matches normalised global);
  Alcotest.(check bool) "source non-global guard rejects a rebound global alias" false
    (matches exported global);
  Alcotest.(check bool) "source guard retains a permitted local alias" true
    (matches exported (Expr.Lit (Literal.Loc "$local")));
  let typed_original = [Asrt.Types [env, Type.ObjectType]] in
  let typed = Engine.MP.retain_precondition_guards ~original:typed_original ~bindings:[] normalised in
  Alcotest.(check bool) "source type rejects a rebound non-object" false
    (matches typed (Expr.num 1.));
  Alcotest.(check bool) "source type retains a permitted object" true
    (matches typed global)

let source_precondition_bindings () =
  let env = Expr.LVar "#source_env" in
  let normalised_loc = Expr.ALoc "normalised_env" in
  let parameter = Expr.PVar "argument" in
  let global = Expr.Lit (Literal.Loc "$lg") in
  let original = [Asrt.Types [env, Type.ObjectType];
    Asrt.Pure (Expr.UnOp (Not, Expr.BinOp (env, Equal, global)))] in
  let normalised = [Asrt.Pure (Expr.BinOp (parameter, ValueEqual, normalised_loc))] in
  let plan assertion = Engine.MP.init (Expr.Set.singleton parameter)
      Expr.Set.empty (Hashtbl.create 0) [assertion, (None, None)] in
  let unbound = Engine.MP.retain_precondition_guards ~original ~bindings:[] normalised in
  Alcotest.(check bool) "unbound source guards cannot become a matching plan" false
    (Result.is_ok (plan unbound));
  let bound = Engine.MP.retain_precondition_guards ~original
      ~bindings:[env, normalised_loc] normalised in
  let matches assertion actual =
    match plan assertion with
    | Error _ -> Alcotest.fail "normalization bindings must make source guards plannable"
    | Ok mp ->
        ReturnMatcher.match_ (return_state ()) (ReturnSubst.init [parameter, actual])
          mp Engine.Matcher.LogicCommand |> List.exists Result.is_ok
  in
  Alcotest.(check bool) "learned source witness retains a local alias" true
    (matches bound (Expr.Lit (Literal.Loc "$local")));
  Alcotest.(check bool) "learned source witness rejects a global alias" false
    (matches bound global);
  Alcotest.(check bool) "learned source witness rejects a non-object" false
    (matches bound (Expr.num 1.));
  List.iter (fun value ->
    let original = [Asrt.Pure (Expr.BinOp (env, ValueEqual, value))] in
    let normalised = [Asrt.Pure (Expr.BinOp (parameter, ValueEqual, env))] in
    let bound = Engine.MP.retain_precondition_guards ~original
        ~bindings:[env, value] normalised in
    Alcotest.(check bool) "normalization bindings preserve exact numeric values" true
      (matches bound value)) [Expr.num 0.; Expr.num (-0.); Expr.num nan];
  let original = [Asrt.Types [env, Type.NumberType]] in
  let bound = Engine.MP.retain_precondition_guards ~original
      ~bindings:[env, Expr.num (-0.)]
      [Asrt.Pure (Expr.BinOp (parameter, ValueEqual, env))] in
  Alcotest.(check bool) "negative-zero witness cannot match positive zero" false
    (matches bound (Expr.num 0.))

(* Normalize a pure footprint through the real state simplifier. The empty
   heap neither owns nor produces cells; its substitutions preserve it. *)
module NormalisationState = Engine.SState.Make (struct
  include Engine.SMemory.Dummy
  let mem_constraints _ = []
  let get_print_info variables _ = (variables, Utils.Containers.SS.empty)
  let substitution_in_place ~pfs:_ ~gamma:_ _ heap =
    [(heap, Expr.Set.empty, [])]
  let assertions ?to_keep:_ _ = []
end)
module NormalisationPredicateBase = Engine.PState.Make (NormalisationState)
module NormalisationPredicateState = struct
  include NormalisationPredicateBase
  (* Model a witness resolved by heap production, after pure normalization.
     The actual simplifier and normalizer must export that newly learned alias. *)
  let simplify ?save ?kill_new_lvars ?matching state =
    let alias = Expr.BinOp (Expr.LVar "#lvar_source_environment", ValueEqual,
      Expr.ALoc "normalisation_environment") in
    let state = match assume_a state [alias] with
      | Some state -> state
      | None -> Alcotest.fail "final normalization alias must be satisfiable" in
    NormalisationPredicateBase.simplify ?save ?kill_new_lvars ?matching state
end
module SourceNormaliser = Engine.Normaliser.Make (NormalisationPredicateState)

let source_normalisation_bindings () =
  let parameter = Expr.PVar "argument" in
  let witness = Expr.LVar "#lvar_source_environment" in
  let global = Expr.Lit (Literal.Loc "$lg") in
  let original = [
    Asrt.Types [parameter, Type.ObjectType];
    Asrt.Pure (Expr.BinOp (parameter, ValueEqual, witness));
    Asrt.Pure (Expr.UnOp (Not, Expr.BinOp (witness, Equal, global)));
  ] in
  let state, subst =
    match SourceNormaliser.normalise_assertion
        ~pred_defs:(Engine.MP.init_pred_defs ()) ~init_data:() original with
    | Ok [result] -> result
    | _ -> Alcotest.fail "expected one normalized pure footprint"
  in
  let actual = Option.get
      (ReturnStore.get (NormalisationPredicateState.get_store state) "argument") in
  let expression = Alcotest.testable Expr.pp Expr.equal in
  Alcotest.(check (option expression))
    "final witness binding agrees with normalized store" (Some actual)
    (ReturnSubst.get subst witness);
  Alcotest.(check (option expression))
    "earlier formal binding follows final simplification" (Some actual)
    (ReturnSubst.get subst parameter);
  let exported = Engine.MP.retain_precondition_guards ~original
      ~bindings:(ReturnSubst.to_list subst)
      (NormalisationPredicateState.to_assertions state) in
  let plan = match Engine.MP.init (Expr.Set.singleton parameter) Expr.Set.empty
      (Hashtbl.create 0) [exported, (None, None)] with
    | Ok plan -> plan
    | Error _ -> Alcotest.fail "normalized source guards must remain plannable"
  in
  let matches value = ReturnMatcher.match_ (return_state ())
      (ReturnSubst.init [parameter, value]) plan Engine.Matcher.LogicCommand
    |> List.exists Result.is_ok in
  Alcotest.(check bool) "normalized source guards retain a local alias" true
    (matches (Expr.Lit (Literal.Loc "$local")));
  Alcotest.(check bool) "normalized source guards reject a global alias" false
    (matches global);
  Alcotest.(check bool) "normalized source guards reject a non-object" false
    (matches (Expr.num 1.))

(* Explicit input alternatives and exact learned witnesses are observable
   matching-plan behavior, including when an earlier atom has to wait. *)
let core_input_readiness () =
  let module MP = Gillian.Abstraction.MP in
  let x = Expr.LVar "#input" and y = Expr.LVar "#value" in
  let z = Expr.LVar "#second" in
  let length = Expr.UnOp (LstLen, x) in
  let core inputs outputs = Asrt.CorePred ("Cell", inputs, outputs) in
  let value_out = [ (y, Expr.PVar "0") ] in
  let check label expected known atoms =
    match expected, MP.s_init_atoms ~preds:(Hashtbl.create 0)
        (Expr.Set.of_list known) atoms with
    | None, Error rest ->
        Alcotest.(check bool) (label ^ ": no assertion silently disappears") true
          (Asrt.equal rest atoms)
    | Some expected, Ok actual ->
        let eq_step (a, outs) (b, outs') = Asrt.equal_atom a b &&
          List.length outs = List.length outs' &&
          List.for_all2 (fun (a,b) (a',b') -> Expr.equal a a' && Expr.equal b b')
            outs outs' in
        Alcotest.(check bool) (label ^ ": exact atom and witness order") true
          (List.length expected = List.length actual &&
           List.for_all2 eq_step expected actual)
    | _ -> Alcotest.fail (label ^ ": wrong eligibility")
  in
  let single label eligible known inputs =
    let atom = core inputs [y] in
    check label (if eligible then Some [(atom,value_out)] else None)
      known [atom]
  in
  single "known variable" true [x] [x];
  single "unknown variable cannot bootstrap from output" false [] [y];
  single "length alone cannot provide a list value" false [length] [x];
  List.iter (fun (label,known,eligible) ->
      single label eligible known [length])
    ["length from list",[x],true; "length from length",[length],true;
     "length with both",[x;length],true; "length missing",[],false];
  single "joint length and list" true [x] [length;x];
  single "joint inputs require actual list" false [length] [length;x];
  single "nested input" true [x] [Expr.EList [length;x]];
  single "nested list not supplied by length" false [length]
    [Expr.EList [length;x]];
  single "bound input variable" true []
    [Expr.ForAll (["#input",None], Expr.BinOp (x,Equal,x))];
  List.iter (fun literal -> single "literal input" true [] [literal])
    [Expr.num nan; Expr.num 0.; Expr.num (-0.); Expr.int 1];
  let output_only = core [] [y] in
  check "original empty-input fallback" (Some [(output_only,[])]) [] [output_only];
  let waiting = core [x] [y] and later = core [Expr.int 1] [x] in
  let last = core [Expr.int 2] [z] in
  check "first eligible atom, then newly enabled earlier atom"
    (Some [(later,[(x,Expr.PVar "0")]);(waiting,value_out);
           (last,[(z,Expr.PVar "0")])]) [] [waiting;later;last];
  let closure = core [x] [Expr.EList [y;z]] in
  check "closure/list witnesses retain field order"
    (Some [(closure,[(y,Expr.BinOp (Expr.PVar "0",LstNth,Expr.int 0));
                    (z,Expr.BinOp (Expr.PVar "0",LstNth,Expr.int 1))])])
    [x] [closure];
  let obligation = Asrt.definedness ~fact:false
      (Expr.BinOp (Expr.Lit (Bool false),And,x)) in
  check "definedness keeps empty scheduling inputs" (Some [(obligation,[])])
    [] [obligation];
  let user = Asrt.pred "Owned" [length] [y] in
  check "encoded user predicate keeps original alternative handling"
    (Some [(user,value_out)]) [length] [user];
  let typed = Asrt.Types [(x,Type.ObjectType)] in
  check "unknown type witness still rejects" None [] [typed];
  check "known type witness" (Some [(typed,[])]) [x] [typed]

(* Observe the real normalizer's exported core arguments. This producer adds
   no coherence constraints itself, so it cannot hide a lost overlap guard. *)
let overlap_produced = ref []
let overlap_produced_gamma = ref []
module OverlapPredicateState = struct
  include NormalisationPredicateBase
  let is_overlapping_asrt name = name = "Overlap"
  let produce state _subst atoms =
    match atoms with
    | [Asrt.CorePred (name, ins, outs)] ->
        overlap_produced := (name, ins, outs) :: !overlap_produced;
        overlap_produced_gamma :=
          Engine.Type_env.to_list (get_typ_env state) :: !overlap_produced_gamma;
        [Ok state]
    | _ -> Alcotest.fail "overlap fixture expects one original core atom"
end
module OverlapNormaliser = Engine.Normaliser.Make (OverlapPredicateState)

let overlapping_guard_normalisation () =
  let core ?(name="Overlap") ins outs = Asrt.CorePred (name,ins,outs) in
  let root = Expr.ALoc "#loc_overlap_root" in
  let a = Expr.ALoc "#loc_overlap_a" and b = Expr.ALoc "#loc_overlap_b" in
  let u = Expr.LVar "#lvar_overlap_u" and v = Expr.LVar "#lvar_overlap_v" in
  let types = Asrt.Types [u,Type.ObjectType; v,Type.ObjectType] in
  (* Core ALoc substitutions need not be exported through the final state.
     Project variable witnesses only; location expectations remain sourced. *)
  let projected subst =
    let variables = ReturnSubst.filter subst (fun key _ -> match key with
        | Expr.LVar _ | PVar _ -> true
        | _ -> false) in
    ReturnSubst.subst_in_expr variables ~partial:true in
  let project_core subst (name,ins,outs) =
    let f = projected subst in name,List.map f ins,List.map f outs in
  let normalise atoms =
    overlap_produced := [];
    overlap_produced_gamma := [];
    match OverlapNormaliser.normalise_assertion
        ~pred_defs:(Engine.MP.init_pred_defs ()) ~init_data:()
        (Engine.Totality.preserve_assertion_domains atoms) with
    | Ok [state,subst] ->
        state,subst,List.map (project_core subst) (List.rev !overlap_produced)
    | _ -> Alcotest.fail "expected one normalized overlap footprint"
  in
  let check label value = Alcotest.(check bool) label true value in
  let eq_list a b = List.length a = List.length b &&
    List.for_all2 Expr.equal a b in
  let eq_core (n,ins,outs) (n',ins',outs') =
    n=n' && eq_list ins ins' && eq_list outs outs' in
  let eq_calls expected actual = List.length expected = List.length actual &&
    List.for_all2 eq_core expected actual in
  let pp_core fmt (name,ins,outs) =
    Fmt.pf fmt "(%S, %a, %a)" name
      (Fmt.Dump.list Expr.pp) ins (Fmt.Dump.list Expr.pp) outs in
  let pp_calls = Fmt.Dump.list pp_core in
  let core_calls = Alcotest.testable pp_calls eq_calls in
  let check_calls label subst source actual =
    let expected = List.map (project_core subst) source in
    Alcotest.check core_calls label expected actual
  in
  (* reduce_types reverses non-types; separate_assertion reverses core atoms
     again. Only the two original metadata locations may represent their
     learned alias; u/v must follow the exported variable substitution. *)
  let _,subst,calls = normalise
      [types; core [root] [a]; core [root] [b]; core [a] [u]; core [b] [v]] in
  Alcotest.(check int) "all four original core atoms are produced" 4
    (List.length calls);
  let expected representative =
    List.map (project_core subst)
      ["Overlap",[root],[representative]; "Overlap",[root],[representative];
       "Overlap",[representative],[u]; "Overlap",[representative],[v]] in
  let expected_a = expected a and expected_b = expected b in
  let tuple_label = "exact original core order, arities and multiplicity remain" in
  let expected =
    if eq_calls expected_a calls then expected_a
    else if eq_calls expected_b calls then expected_b
    else Alcotest.failf "%s: expected either %a or %a; actual %a"
        tuple_label pp_calls expected_a pp_calls expected_b pp_calls calls in
  Alcotest.check core_calls tuple_label expected calls;
  (match calls with
   | [(_, [root1], [meta1]); (_, [root2], [meta2]);
      (_, [left], [out1]); (_, [right], [out2])] ->
       check "same-input metadata establishes the location alias"
         (Expr.equal left right && Expr.equal meta1 meta2 &&
          Expr.equal left meta1);
       check "possible-alias output guard survives until that alias is learned"
         (Expr.equal out1 out2);
       check "unrelated root location and production order remain"
         (Expr.equal root1 (projected subst root) && Expr.equal root2 root1 &&
          not (Expr.equal root1 left))
   | _ -> Alcotest.fail "expected original core arities and source order");
  let _,subst,calls = normalise [core [a] [Expr.Lit Null]; core [b] [Expr.Lit Null]] in
  check_calls "tautological null outputs preserve both original atoms in order"
    subst ["Overlap",[a],[Expr.Lit Null]; "Overlap",[b],[Expr.Lit Null]] calls;
  let state,subst,calls = normalise
      [types; core ~name:"Exclusive" [root] [u];
       core ~name:"Exclusive" [root] [v]] in
  check_calls "non-overlapping original core order, arities and multiplicity remain"
    subst ["Exclusive",[root],[u]; "Exclusive",[root],[v]] calls;
  check "non-overlapping predicates keep their distinct output witnesses"
    (not (Expr.equal (projected subst u) (projected subst v)));
  let established_type expr = match projected subst expr with
    | Expr.LVar name | PVar name ->
        Engine.Type_env.get (OverlapPredicateState.get_typ_env state) name
    | ALoc _ -> Some Type.ObjectType
    | Lit literal -> Some (Literal.type_of literal)
    | _ -> None
  in
  check "original output types remain established"
    (established_type u = Some Type.ObjectType &&
     established_type v = Some Type.ObjectType);
  let _,subst,calls = normalise [core [] []; core [] []] in
  check_calls "empty conjunction/disjunction fallback retains both core atoms"
    subst ["Overlap",[],[]; "Overlap",[],[]] calls;
  let _,subst,calls = normalise [core [root] [Expr.num 0.]; core [root] [Expr.num (-0.)]] in
  check_calls "signed-zero atoms keep original core order, arities and multiplicity"
    subst ["Overlap",[root],[Expr.num 0.]; "Overlap",[root],[Expr.num (-0.)]] calls;
  check "ordinary equality does not rewrite the original signed-zero outputs"
    (match calls with [(_,_,[plus]);(_,_,[minus])] ->
       Expr.equal minus (Expr.num (-0.)) && Expr.equal plus (Expr.num 0.)
     | _ -> false);
  (* The optimization also runs in legacy mode. Preserve a type learned by
     the old guard simplifier instead of discarding it with a copied gamma. *)
  let list_name = "#lvar_overlap_inferred_list" in
  let length = Expr.UnOp (LstLen,Expr.LVar list_name) in
  let total = !Utils.Config.Verification.total in
  Utils.Config.Verification.total := false;
  let _,subst,calls = Fun.protect
      ~finally:(fun () -> Utils.Config.Verification.total := total)
      (fun () -> normalise [core [length] [Expr.Lit Null]]) in
  Alcotest.(check int) "speculative-type control preserves the core atom" 1
    (List.length calls);
  check_calls "speculative-type core input and output remain"
    subst ["Overlap",[length],[Expr.Lit Null]] calls;
  check "tautology with new typing is delegated to the original simplifier"
    (match projected subst (Expr.LVar list_name),!overlap_produced_gamma with
     | Expr.LVar name,[gamma] -> List.assoc_opt name gamma = Some Type.ListType
     | _ -> false);
  let partial = Expr.BinOp (Expr.EList [],LstNth,Expr.int 0) in
  (match normalise [core [partial] [Expr.Lit Null]] with
   | _ -> Alcotest.fail "undefined original core input must not be erased"
   | exception Gillian.Utils.Gillian_result.Exc.Gillian_error
       (AnalysisFailures [{msg; _}]) ->
       check "original definedness is checked before null-output tautology filtering"
         (String.starts_with ~prefix:"Produced assertion is not proved defined:" msg);
       Alcotest.(check int) "undefined core input never reaches heap production" 0
         (List.length !overlap_produced))

let stable_pfs_duplicates () =
  let module P = Engine.PFS in
  let rec oracle seen = function
    | [] -> []
    | value :: rest when List.exists (Expr.equal value) seen -> oracle seen rest
    | value :: rest -> value :: oracle (value :: seen) rest
  in
  let a () = Expr.BinOp (Expr.LVar "#dedup_a", Equal, Expr.int 1) in
  let b = Expr.LVar "#dedup_b" in
  let cases = [ []; [a ()]; [a ();a ();a ()];
    [a ();b;a ();b;a ()]; [b;a ();a ();a ()];
    List.init 64 (fun _ -> a ());
    [Expr.num 0.;Expr.num (-0.);Expr.num 0.;Expr.num (-0.)] ] in
  List.iteri (fun i values ->
      let label suffix = Printf.sprintf "dedup case %d %s" i suffix in
      let expected = oracle [] values in
      let actual = P.of_list values in
      P.remove_duplicates actual;
      let check_queue suffix expected queue =
        Alcotest.(check int) (label (suffix ^ " length"))
          (List.length expected) (P.length queue);
        Alcotest.(check bool) (label (suffix ^ " first objects and order")) true
          (List.equal ( == ) expected (P.to_list queue))
      in
      check_queue "initial" expected actual;
      P.remove_duplicates actual;
      check_queue "idempotent" expected actual;
      let appended = Expr.LVar "#dedup_append" in
      P.extend actual appended;
      P.extend actual appended;
      check_queue "reachable append" (expected @ [appended]) actual;
      let copied = P.copy actual in
      let tail = Expr.LVar "#dedup_merge" in
      let donor = P.of_list [tail] in
      P.merge_into_left actual donor;
      check_queue "merge tail" (expected @ [appended;tail]) actual;
      check_queue "consumed donor" [] donor;
      P.clear actual;
      check_queue "cleared" [] actual;
      P.extend actual b;
      check_queue "reused" [b] actual;
      check_queue "copy independent" (expected @ [appended]) copied)
    cases;
  (* Fresh, all-unique queues avoid the legacy metadata bug. This measures only
     duplicate removal, not the complete sanitizer or caller preparation. *)
  List.iter (fun size ->
      let values = List.init size (fun i ->
          Expr.LVar (Printf.sprintf "#dedup_benchmark_%06d" i)) in
      let legacy = Utils.Ext_list.of_list values in
      let current = P.of_list values in
      let start = Sys.time () in
      Utils.Ext_list.remove_duplicates ~equal:Expr.equal legacy;
      let legacy_cpu = Sys.time () -. start in
      let start = Sys.time () in
      P.remove_duplicates current;
      let current_cpu = Sys.time () -. start in
      Alcotest.(check bool) "benchmark preserves exact first objects" true
        (List.equal ( == ) values (P.to_list current));
      Alcotest.(check int) "benchmark preserves queue length" size (P.length current);
      Printf.printf "PFS_DEDUP_BENCHMARK size=%d legacy_cpu=%.6f current_cpu=%.6f\n%!"
        size legacy_cpu current_cpu)
    [1024;4096;8192]

let pfs_structural_identity () =
  let f bits = Expr.num (Int64.float_of_bits bits) in
  let string units = Expr.Lit (Utf16String (Utils.Utf16.of_canonical (Utils.Utf16.of_code_units units))) in
  let x = Expr.LVar "#dedup_x" and y = Expr.LVar "#dedup_y" in
  let values =
    [ Expr.Lit Undefined; Expr.Lit Null; Expr.Lit Empty; Expr.Lit Nono;
      Expr.Lit (Constant Pi); Expr.Lit (Constant Random);
      Expr.Lit (Bool false); Expr.Lit (Bool true);
      Expr.int 0; Expr.Lit (Int (Z.of_string "999999999999999999999999999"));
      Expr.num 0.; Expr.num (-0.); Expr.num infinity; Expr.num neg_infinity;
      f 1L; f 0x7ff8000000000001L; f 0x7ff8000000000001L;
      f 0x7ff8000000000002L; f 0x7ff0000000000001L; f 0xfff8000000000001L;
      Expr.Lit (String "\000\255"); Expr.Lit (Loc "#dedup_loc");
      Expr.Lit (Type NumberType); Expr.Lit (LList [Num 0.;Num (-0.)]);
      string [0;0xd800;0xdc00]; string [0;0xdc00;0xd800];
      string [0;0xd800;0xdc00]; Expr.PVar "dedup_x"; x; y; Expr.ALoc "#dedup_x";
      Expr.UnOp (Not,x); Expr.UnOp (TypeOf,x);
      Expr.BinOp (x,Equal,y); Expr.BinOp (x,ValueEqual,y);
      Expr.BinOp (y,Equal,x); Expr.LstSub (x,Expr.int 0,Expr.int 1);
      Expr.NOp (LstCat,[x;y]); Expr.NOp (LstCat,[y;x]);
      Expr.EList [x;y]; Expr.EList [y;x]; Expr.ESet [x;y]; Expr.ESet [y;x];
      Expr.Exists (["#dedup_x",None],x);
      Expr.ForAll (["#dedup_x",None],x);
      Expr.ForAll (["#dedup_y",None],y);
      Expr.ForAll (["#dedup_x",Some NumberType],x);
      Expr.ConstructorApp ("Dedup",[x;y]); Expr.FuncApp ("Dedup",[x;y]);
      Expr.Cases (x,["Dedup",["#dedup_y"],y]) ]
  in
  List.iter (fun a -> List.iter (fun b ->
      Alcotest.(check bool) "compare zero agrees with exact expression identity"
        (Expr.equal a b) (Expr.compare a b = 0)) values) values;
  let pfs = Engine.PFS.of_list (values @ List.rev values @ values) in
  let rec first seen = function
    | [] -> []
    | value :: rest when List.exists (Expr.equal value) seen -> first seen rest
    | value :: rest -> value :: first (value :: seen) rest
  in
  let expected = first [] (values @ List.rev values @ values) in
  Engine.PFS.remove_duplicates pfs;
  Alcotest.(check bool) "structural corpus preserves first objects and order" true
    (List.equal ( == ) expected (Engine.PFS.to_list pfs));
  Alcotest.(check int) "structural corpus retains exact queue length"
    (List.length expected) (Engine.PFS.length pfs)

let boolean_root_reduction () =
  let open Type in
  let module Reduction = Gillian.Logic.Reduction in
  let module Gamma = Gillian.Symbolic.Type_env in
  let module P = Engine.PFS in
  let check label actual = Alcotest.(check bool) label true actual in
  let equal label expected actual = check label (Expr.equal expected actual) in
  let eq a b = Expr.BinOp (a, Equal, b) in
  let gamma_snapshot gamma =
    List.sort (fun (a, _) (b, _) -> String.compare a b) (Gamma.to_list gamma)
  in
  let gamma = Gamma.init () in
  List.iteri (fun i typ ->
      Gamma.update gamma (Printf.sprintf "#boolean_unrelated_%04d" i) typ)
    (List.init 4096 (fun i ->
         match i mod 4 with
         | 0 -> BooleanType | 1 -> ListType | 2 -> ObjectType | _ -> NumberType));
  let conflict = Expr.LVar "#boolean_conflict" in
  Gamma.update gamma "#boolean_conflict" NumberType;
  let partial = eq (Expr.BinOp (Expr.EList [], LstNth, Expr.int 0)) Expr.true_ in
  let facts = [eq conflict Expr.true_; eq conflict Expr.false_; partial; Expr.false_] in
  let pfs = P.of_list facts in
  let before_gamma = gamma_snapshot gamma in
  List.iter (fun matching -> List.iter (fun reduce_lvars ->
      List.iter (fun value ->
          let label suffix = Printf.sprintf
              "Boolean root %b matching=%b reduce_lvars=%b %s"
              value matching reduce_lvars suffix in
          let input = Expr.Lit (Bool value) in
          let result = Reduction.reduce_lexpr ~matching ~reduce_lvars ~pfs ~gamma input in
          check (label "retains original object") (result == input);
          equal (label "retains exact value") (Expr.bool value) result;
          check (label "preserves PFS objects and order")
            (List.equal ( == ) facts (P.to_list pfs));
          Alcotest.(check int) (label "preserves PFS length") (List.length facts) (P.length pfs);
          check (label "preserves all gamma bindings")
            (before_gamma = gamma_snapshot gamma)) [false;true]) [false;true]) [false;true];
  List.iter (fun value ->
      let input = Expr.Lit (Bool value) in
      check (Printf.sprintf "Boolean root %b with default contexts retains object" value)
        (Reduction.reduce_lexpr input == input)) [false;true];
  let reduce expression = Reduction.reduce_lexpr expression in
  let pi = Expr.num (4. *. atan 1.) in
  equal "non-Boolean static constant still resolves" pi (reduce (Expr.Lit (Constant Pi)));
  equal "dynamic constant remains symbolic" (Expr.Lit (Constant Random))
    (reduce (Expr.Lit (Constant Random)));
  equal "nonliteral integer arithmetic still reduces" (Expr.int 5)
    (reduce (Expr.BinOp (Expr.int 2, IPlus, Expr.int 3)));
  let list = Expr.EList [Expr.Lit (Constant Pi);
      Expr.BinOp (Expr.int 2, IPlus, Expr.int 3); Expr.num (-0.)] in
  equal "list elements normalize without losing signed zero"
    (Expr.EList [pi;Expr.int 5;Expr.num (-0.)]) (reduce list);
  equal "list length still reduces" (Expr.int 3) (reduce (Expr.UnOp (LstLen,list)));
  equal "valid list index still reduces" (Expr.int 5)
    (reduce (Expr.BinOp (list,LstNth,Expr.int 1)));
  let rejects label reduce expression =
    check label (try ignore (reduce expression); false
      with Reduction.ReductionException _ -> true)
  in
  rejects "non-Boolean literal cannot become a Boolean integer" reduce
    (Expr.UnOp (BoolToInt,Expr.int 1));
  let bad_gamma = Gamma.init () in
  Gamma.update bad_gamma "#boolean_bad" NumberType;
  rejects "symbolic invalid Boolean typing still rejects"
    (fun expression -> Reduction.reduce_lexpr ~gamma:bad_gamma expression)
    (Expr.UnOp (BoolToInt,Expr.LVar "#boolean_bad"));
  rejects "list operation on a non-list still rejects" reduce
    (Expr.UnOp (LstLen,Expr.int 1));
  List.iter (fun (label,index) ->
      rejects label reduce (Expr.BinOp (Expr.EList [Expr.true_],LstNth,index)))
    ["out-of-bounds list index still rejects",Expr.int 1;
     "negative list index still rejects",Expr.int (-1);
     "float list index still rejects",Expr.num 0.];
  List.iter (fun (label,left,op,expected) ->
      equal label expected (reduce (Expr.BinOp (left,op,partial))))
    ["false conjunction skips undefined right operand",Expr.false_,And,Expr.false_;
     "true disjunction skips undefined right operand",Expr.true_,Or,Expr.true_;
     "false implication skips undefined right operand",Expr.false_,Impl,Expr.true_];
  List.iter (fun (label,expression) -> rejects label reduce expression)
    ["true conjunction requires defined right operand",Expr.BinOp (Expr.true_,And,partial);
     "false disjunction requires defined right operand",Expr.BinOp (Expr.false_,Or,partial);
     "true implication requires defined right operand",Expr.BinOp (Expr.true_,Impl,partial);
     "false conjunction cannot erase undefined left operand",Expr.BinOp (partial,And,Expr.false_);
     "true disjunction cannot erase undefined left operand",Expr.BinOp (partial,Or,Expr.true_);
     "negation cannot invert undefined operand",Expr.UnOp (Not,partial)];
  let variable = Expr.LVar "#boolean_control" in
  let control_gamma = Gamma.init () in
  Gamma.update control_gamma "#boolean_control" IntType;
  let control_pfs = P.of_list [eq variable (Expr.int 7)] in
  List.iter (fun matching -> List.iter (fun reduce_lvars ->
      let label suffix = Printf.sprintf "nonliteral matching=%b reduce_lvars=%b %s"
          matching reduce_lvars suffix in
      equal (label "respects variable flag") (if reduce_lvars then Expr.int 7 else variable)
        (Reduction.reduce_lexpr ~matching ~reduce_lvars ~pfs:control_pfs ~gamma:control_gamma variable);
      let locations = eq (Expr.ALoc "#boolean_a") (Expr.ALoc "#boolean_b") in
      equal (label "respects location matching flag") (if matching then locations else Expr.false_)
        (Reduction.reduce_lexpr ~matching ~reduce_lvars locations)) [false;true]) [false;true];
  let bound = "#boolean_bound" in
  let binder_gamma = Gamma.init () in
  Gamma.update binder_gamma bound IntType;
  let binder_facts = [eq (Expr.LVar bound) (Expr.int 7)] in
  let binder_pfs = P.of_list binder_facts in
  let before_binder_gamma = gamma_snapshot binder_gamma in
  List.iter (fun universal -> List.iter (fun binder_type ->
      let label suffix = Printf.sprintf "%s %s binder %s"
          (if universal then "universal" else "existential")
          (if Option.is_some binder_type then "typed" else "untyped") suffix in
      let body = eq (Expr.LVar bound) (Expr.int 7) in
      let quantified = if universal then Expr.ForAll ([bound,binder_type],body)
        else Expr.Exists ([bound,binder_type],body) in
      equal (label "shadows outer equality") quantified
        (Reduction.reduce_lexpr ~reduce_lvars:true ~pfs:binder_pfs ~gamma:binder_gamma quantified);
      check (label "preserves outer gamma") (before_binder_gamma = gamma_snapshot binder_gamma);
      check (label "preserves outer PFS objects")
        (List.equal ( == ) binder_facts (P.to_list binder_pfs))) [None;Some IntType]) [false;true];
  let boolean_binder_gamma = Gamma.init () in
  Gamma.update boolean_binder_gamma "#boolean_outer_context" BooleanType;
  rejects "declared non-Boolean binder rejects Boolean conversion"
    (fun expression -> Reduction.reduce_lexpr ~gamma:boolean_binder_gamma expression)
    (Expr.ForAll ([bound,Some NumberType],
       eq (Expr.UnOp (BoolToInt,Expr.LVar bound)) (Expr.int 1)))

let closed_leaf_overlap () =
  let module Gamma = Gillian.Symbolic.Type_env in
  let module Reduction = Gillian.Logic.Reduction in
  let module P = Engine.PFS in
  let observations = ref [] in
  (* Record actual public normalizer states without adding any overlap facts. *)
  let module State = struct
    include NormalisationPredicateBase
    let is_overlapping_asrt name = name = "ClosedOverlap"
    let produce state _subst = function
      | [Asrt.CorePred (name,ins,outs)] ->
          let pfs = get_pfs state and gamma = get_typ_env state in
          observations :=
            ((name,ins,outs),pfs,gamma,P.to_list pfs,Gamma.to_list gamma)
            :: !observations;
          [Ok state]
      | _ -> Alcotest.fail "closed-leaf fixture expects one original core atom"
  end in
  let module N = Engine.Normaliser.Make (State) in
  let check label actual = Alcotest.(check bool) label true actual in
  let snapshot gamma =
    List.sort (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  let projected subst =
    let variables = ReturnSubst.filter subst (fun key _ -> match key with
        | Expr.LVar _ | PVar _ -> true | _ -> false) in
    ReturnSubst.subst_in_expr variables ~partial:true in
  let project subst (name,ins,outs) =
    let f = projected subst in name,List.map f ins,List.map f outs in
  let eq_core (name,ins,outs) (name',ins',outs') =
    name = name' && List.equal Expr.equal ins ins'
    && List.equal Expr.equal outs outs' in
  let pp_core fmt (name,ins,outs) = Fmt.pf fmt "(%S,%a,%a)" name
      (Fmt.Dump.list Expr.pp) ins (Fmt.Dump.list Expr.pp) outs in
  let calls = Alcotest.testable (Fmt.Dump.list pp_core) (List.equal eq_core) in
  let core ?(name="ClosedOverlap") ins outs = Asrt.CorePred (name,ins,outs) in
  let normalise atoms =
    observations := [];
    match N.normalise_assertion ~pred_defs:(Engine.MP.init_pred_defs ())
        ~init_data:() (Engine.Totality.preserve_assertion_domains atoms) with
    | Ok [state,subst] -> state,subst,List.rev !observations
    | _ -> Alcotest.fail "expected one actual closed-leaf normalized state" in
  let actual_calls subst observed =
    List.map (fun (atom,_,_,_,_) -> project subst atom) observed in
  let a = Expr.ALoc "#loc_closed_a" and b = Expr.ALoc "#loc_closed_b" in
  let x = Expr.Lit (Literal.Loc "$closed_x")
  and y = Expr.Lit (Literal.Loc "$closed_y") in
  let outputs = ["abstract",Expr.ALoc "#loc_closed_metadata";
    "literal",Expr.Lit (Literal.Loc "$closed_metadata");
    "null",Expr.Lit Literal.Null] in
  let inputs = ["abstract diagonal",a,a; "literal diagonal",x,x;
    "abstract pair",a,b; "abstract/literal",a,x;
    "literal/abstract",x,a; "literal pair",x,y] in
  let bindings = List.init 512 (fun i ->
      let typ = if i < 64 then Type.NumberType else match i mod 4 with
        | 0 -> Type.NumberType | 1 -> Type.BooleanType
        | 2 -> Type.ListType | _ -> Type.ObjectType in
      Expr.LVar (Printf.sprintf "#lvar_closed_context_%04d" i),typ) in
  let context_pfs = List.init 64 (fun i ->
      let variable,_ = List.nth bindings i in
      Asrt.Pure (Expr.BinOp (variable,FLessThan,Expr.num 100.))) in
  let context = Asrt.Types bindings :: context_pfs in
  List.iter (fun (input_name,left,right) ->
      List.iter (fun (output_name,output) ->
          let label = input_name ^ "/" ^ output_name in
          let state,subst,observed = normalise
              (context @ [core [left] [output];core [right] [output]]) in
          let baseline,_,_ = normalise (context @
              [core ~name:"Exclusive" [left] [output];
               core ~name:"Exclusive" [right] [output]]) in
          Alcotest.check calls (label ^ ": original ordered core footprint")
            (List.map (project subst)
               ["ClosedOverlap",[left],[output];
                "ClosedOverlap",[right],[output]])
            (actual_calls subst observed);
          check (label ^ ": unrelated gamma agrees with nonoverlap baseline")
            (snapshot (State.get_typ_env state) = snapshot (State.get_typ_env baseline)
             && List.length (snapshot (State.get_typ_env state)) = 512);
          check (label ^ ": unrelated PFS agrees with nonoverlap baseline")
             (List.equal Expr.equal (P.to_list (State.get_pfs state))
               (P.to_list (State.get_pfs baseline))
             && P.length (State.get_pfs state) >= 64);
          check (label ^ ": production context objects and formula order remain")
            (match observed with
             | [(_,pfs,gamma,first,types);(_,pfs',gamma',second,types')] ->
                 pfs == pfs' && pfs == State.get_pfs state
                 && gamma == gamma' && gamma == State.get_typ_env state
                 && List.equal ( == ) first second && types = types'
             | _ -> false)) outputs) inputs;
  let root = Expr.ALoc "#loc_closed_root" in
  let u = Expr.LVar "#lvar_closed_u" and v = Expr.LVar "#lvar_closed_v" in
  let _,subst,observed = normalise
      [Asrt.Types [u,Type.ObjectType;v,Type.ObjectType];
       core [root] [a];core [root] [b];core [a] [u];core [b] [v]] in
  let actual = actual_calls subst observed in
  let expected representative = List.map (project subst)
      ["ClosedOverlap",[root],[representative];
       "ClosedOverlap",[root],[representative];
       "ClosedOverlap",[representative],[u];
       "ClosedOverlap",[representative],[v]] in
  check "alias-sensitive guards preserve the full ordered four-atom footprint"
    (List.equal eq_core (expected a) actual || List.equal eq_core (expected b) actual);
  check "different original outputs still establish the A/B and u/v aliases"
    (match actual with
     | [(_,[r1],[m1]);(_,[r2],[m2]);(_,[i1],[o1]);(_,[i2],[o2])] ->
         Expr.equal r1 root && Expr.equal r2 root
         && Expr.equal m1 m2 && Expr.equal m1 i1 && Expr.equal i1 i2
         && Expr.equal o1 o2 && not (Expr.equal root i1)
     | _ -> false);
  let unknown = Expr.LVar "#lvar_closed_unknown_output" in
  let state,subst,observed = normalise [core [a] [unknown]] in
  Alcotest.check calls "unknown output remains an original core witness"
    [project subst ("ClosedOverlap",[a],[unknown])] (actual_calls subst observed);
  check "unknown output does not acquire a speculative type"
    (match projected subst unknown with
     | Expr.LVar name -> Gamma.get (State.get_typ_env state) name = None
     | _ -> false);
  let nan_value = Expr.num (Int64.float_of_bits 0x7ff8000000000001L) in
  let _,subst,observed = normalise [core [a] [nan_value]] in
  Alcotest.check calls "NaN output bits remain in the actual core footprint"
    [project subst ("ClosedOverlap",[a],[nan_value])] (actual_calls subst observed);
  (* These public Reduction/PFS controls retain original guard objects. The
     private generated overlap PFS is not exported by normalise_assertion. *)
  let guard i1 i2 o1 o2 = Expr.BinOp
      (Expr.UnOp (Not,Expr.BinOp (i1,Equal,i2)),Or,
       Expr.BinOp (o1,Equal,o2)) in
  let gamma = Gamma.init () and pfs = P.init () in
  let unknown_guard = guard a a unknown unknown in
  check "untyped self-output guard is not classified true by the reducer"
    (not (Expr.equal Expr.true_
       (Reduction.reduce_lexpr ~matching:true ~pfs ~gamma unknown_guard)));
  check "bit-identical NaN self-output guard reduces false"
    (Expr.equal Expr.false_ (Reduction.reduce_lexpr ~matching:true ~pfs ~gamma
       (guard a a nan_value nan_value)));
  let m = Expr.ALoc "#loc_closed_m" and n = Expr.ALoc "#loc_closed_n" in
  let forward = guard a b m n and reverse = guard b a n m in
  List.iter (fun original ->
      check (if original == forward then "forward alias guard remains unknown"
             else "reverse alias guard remains unknown")
        (not (Expr.equal Expr.true_
           (Reduction.reduce_lexpr ~matching:true ~pfs ~gamma original)));
      P.extend pfs original) [forward;reverse];
  check "both directional guard objects retain their insertion order"
    (List.equal ( == ) [forward;reverse] (P.to_list pfs));
  let directional = Expr.BinOp (m,Equal,n) in
  let facts = P.of_list [directional] in
  check "forward output fact resolves only the forward guard"
    (Expr.equal Expr.true_
       (Reduction.reduce_lexpr ~matching:true ~pfs:facts ~gamma forward));
  check "reverse guard still uses its own directional PFS membership"
    (not (Expr.equal Expr.true_
       (Reduction.reduce_lexpr ~matching:true ~pfs:facts ~gamma reverse)));
  check "directional reduction leaves the original PFS object and gamma unchanged"
    (List.equal ( == ) [directional] (P.to_list facts) && snapshot gamma = []);
  let partial = Expr.UnOp (Car,Expr.EList []) in
  (match Reduction.reduce_lexpr ~matching:true ~pfs:(P.init ()) ~gamma
      (guard a a partial partial) with
   | _ -> Alcotest.fail "partial self-output guard must retain its reduction error"
   | exception Reduction.ReductionException _ ->
       check "partial self-output guard retains the original reduction error" true);
  (match normalise [core [a] [partial]] with
   | _ -> Alcotest.fail "partial original output must not reach heap production"
   | exception Gillian.Utils.Gillian_result.Exc.Gillian_error
       (AnalysisFailures [{msg;_}]) ->
       check "partial original output is rejected before overlap classification"
         (String.starts_with ~prefix:"Produced assertion is not proved defined:" msg);
       check "partial original output never reaches core production"
         (!observations = []));
  let list_name = "#lvar_closed_inferred_list" in
  let length = Expr.UnOp (LstLen,Expr.LVar list_name) in
  let total = !Utils.Config.Verification.total in
  Utils.Config.Verification.total := false;
  let state,subst,observed = Fun.protect
      ~finally:(fun () -> Utils.Config.Verification.total := total)
      (fun () -> normalise [core [length] [Expr.Lit Literal.Null]]) in
  Alcotest.check calls "inferred-list fallback preserves the original core atom"
    [project subst ("ClosedOverlap",[length],[Expr.Lit Literal.Null])]
    (actual_calls subst observed);
  check "inferred-list fallback retains downstream gamma inference"
    (match projected subst (Expr.LVar list_name) with
     | Expr.LVar name -> Gamma.get (State.get_typ_env state) name = Some Type.ListType
     | _ -> false);
  List.iter (fun (label,atoms,expected) ->
      let _,subst,observed = normalise atoms in
      Alcotest.check calls label (List.map (project subst) expected)
        (actual_calls subst observed))
    ["empty-arity fallback retains original order and multiplicity",
       [core [] [];core [] []],["ClosedOverlap",[],[];"ClosedOverlap",[],[]];
     "multi-arity fallback retains original inputs and outputs",
       [core [a;b] [Expr.Lit Literal.Null;x];
        core [b;a] [Expr.Lit Literal.Null;x]],
       ["ClosedOverlap",[a;b],[Expr.Lit Literal.Null;x];
        "ClosedOverlap",[b;a],[Expr.Lit Literal.Null;x]]];
  List.iter (fun (label,atoms) ->
      match normalise atoms with
      | _ -> Alcotest.fail "mismatched overlap arity must still raise"
      | exception Failure msg -> check label
          (msg = "DEATH. generate_overlapping_constraints" && !observations = []))
    ["mismatched input arity fails before original core production",
       [core [a] [Expr.Lit Literal.Null];core [b;a] [Expr.Lit Literal.Null]];
     "mismatched output arity fails before original core production",
       [core [a] [Expr.Lit Literal.Null];core [b] [Expr.Lit Literal.Null;x]]]

let closed_guard_snapshot () =
  let module Reduction = Gillian.Logic.Reduction in
  let module Gamma = Gillian.Symbolic.Type_env in
  let module P = Engine.PFS in
  let check label actual = Alcotest.(check bool) label true actual in
  let expressions = Alcotest.testable Expr.pp Expr.equal in
  let eq a b = Expr.BinOp (a,Equal,b) in
  let snapshot gamma = List.sort
      (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  (* Core arguments use the original private reducer with its own fresh
     input snapshot. This public assertion route repeats the fixedpoint and
     has default reduce_lvars=false; the admitted roots contain no variables. *)
  let reference ~matching ~pfs ~gamma expression =
    match Reduction.reduce_assertion ~matching ~pfs ~gamma
        [Asrt.CorePred ("SnapshotReference",[expression],[])] with
    | [Asrt.CorePred ("SnapshotReference",[result],[])] -> result
    | _ -> Alcotest.fail "original assertion reducer changed the reference footprint" in
  let rec location_leaves = function
    | (Expr.ALoc _ | Expr.Lit (Literal.Loc _ | Literal.Null)) as leaf -> [leaf]
    | Expr.UnOp (_,child) -> location_leaves child
    | Expr.BinOp (left,_,right) -> location_leaves left @ location_leaves right
    | _ -> [] in
  let gamma = Gamma.init () in
  List.iteri (fun i typ ->
      Gamma.update gamma (Printf.sprintf "#snapshot_unrelated_%04d" i) typ)
    (List.init 2048 (fun i -> match i mod 4 with
         | 0 -> Type.BooleanType | 1 -> Type.ListType
         | 2 -> Type.ObjectType | _ -> Type.NumberType));
  (* These deliberately disagree with the static ALoc/Loc leaf types. *)
  Gamma.update gamma "#loc_snapshot_a" Type.NumberType;
  Gamma.update gamma "#loc_snapshot_b" Type.ListType;
  Gamma.update gamma "$snapshot_x" Type.BooleanType;
  Gamma.update gamma "#snapshot_conflict" Type.NumberType;
  let before_gamma = snapshot gamma in
  let conflict = Expr.LVar "#snapshot_conflict" in
  let partial = Expr.UnOp (Car,Expr.EList []) in
  let facts = [eq conflict Expr.true_; eq conflict Expr.false_;
    eq partial (Expr.Lit Literal.Null); Expr.false_] in
  let compare label expression facts =
    List.iter (fun matching -> List.iter (fun reduce_lvars ->
        let label suffix = Printf.sprintf "%s matching=%b reduce_lvars=%b %s"
            label matching reduce_lvars suffix in
        let actual_gamma = Gamma.copy gamma and reference_gamma = Gamma.copy gamma in
        let before = snapshot actual_gamma in
        let actual_pfs = P.of_list facts in
        let reference_pfs = P.copy actual_pfs in
        let actual = Reduction.reduce_lexpr ~matching ~reduce_lvars
            ~pfs:actual_pfs ~gamma:actual_gamma expression in
        let expected = reference ~matching ~pfs:reference_pfs
            ~gamma:reference_gamma expression in
        Alcotest.check expressions (label "agrees with original snapshot normal form") expected actual;
        check (label "retains the same original location leaf objects")
          (List.equal ( == ) (location_leaves expected) (location_leaves actual));
        check (label "preserves both gamma mappings")
          (before = snapshot actual_gamma && before = snapshot reference_gamma);
        check (label "preserves PFS objects order and length")
          (List.equal ( == ) facts (P.to_list actual_pfs)
           && List.equal ( == ) facts (P.to_list reference_pfs)
           && P.length actual_pfs = List.length facts
           && P.length reference_pfs = List.length facts)) [false;true]) [false;true] in
  let a = Expr.ALoc "#loc_snapshot_a" and b = Expr.ALoc "#loc_snapshot_b" in
  let x = Expr.Lit (Literal.Loc "$snapshot_x")
  and y = Expr.Lit (Literal.Loc "$snapshot_y") in
  let null = Expr.Lit Literal.Null in
  List.iter (fun (label,left,right) -> compare label (eq left right) facts)
    ["abstract identity",a,a; "abstract pair",a,b;
     "literal identity",x,x; "literal pair",x,y; "null identity",null,null;
     "abstract/literal",a,x; "literal/abstract",x,a;
     "abstract/null",a,null; "null/abstract",null,a;
     "literal/null",x,null; "null/literal",null,x];
  let m = Expr.ALoc "#loc_snapshot_m" and n = Expr.ALoc "#loc_snapshot_n" in
  List.iter (fun (label,expression) -> compare label expression facts)
    ["double negation",Expr.UnOp (Not,Expr.UnOp (Not,eq a b));
     "nested conjunction",Expr.BinOp (eq a b,And,Expr.UnOp (Not,eq m n));
     "nested De Morgan",Expr.UnOp (Not,Expr.BinOp
         (eq a b,And,Expr.BinOp (eq m n,Or,eq null null)));
     "nested literal Booleans",Expr.BinOp (Expr.false_,Or,
         Expr.BinOp (Expr.true_,And,Expr.UnOp (Not,eq a b)))];
  let positive = eq a b and negative = Expr.UnOp (Not,eq a b) in
  compare "positive conjunct membership" (Expr.BinOp (positive,And,eq m n)) (positive :: facts);
  compare "negative conjunct membership" (Expr.BinOp (positive,And,eq m n)) (negative :: facts);
  compare "negative disjunct membership" (Expr.BinOp (positive,Or,eq m n)) (negative :: facts);
  let guard i1 i2 o1 o2 = Expr.BinOp (Expr.UnOp (Not,eq i1 i2),Or,eq o1 o2) in
  let forward = guard a b m n and reverse = guard b a n m in
  let directional = eq m n in
  compare "forward directional guard" forward (directional :: facts);
  compare "reverse directional guard" reverse (directional :: facts);
  let directional_pfs = P.of_list [directional;forward;reverse] in
  let reduce expression = Reduction.reduce_lexpr ~matching:true
      ~pfs:directional_pfs ~gamma expression in
  check "forward directional fact resolves the forward guard"
    (Expr.equal Expr.true_ (reduce forward));
  check "reverse directional guard is not inferred from the forward output fact"
    (not (Expr.equal Expr.true_ (reduce reverse)));
  check "directional reduction preserves original PFS order and gamma"
    (List.equal ( == ) [directional;forward;reverse] (P.to_list directional_pfs)
     && before_gamma = snapshot gamma);
  List.iter (fun value ->
      let input = Expr.bool value in
      check (Printf.sprintf "literal Boolean %b still returns its original object" value)
        (Reduction.reduce_lexpr ~matching:true ~reduce_lvars:true
           ~pfs:(P.of_list facts) ~gamma input == input)) [false;true];
  let variable = Expr.LVar "#snapshot_variable" in
  let variable_gamma = Gamma.init () in
  Gamma.update variable_gamma "#snapshot_variable" Type.IntType;
  let variable_fact = eq variable (Expr.int 7) in
  let variable_pfs = P.of_list [variable_fact] in
  List.iter (fun reduce_lvars ->
      Alcotest.check expressions
        (Printf.sprintf "excluded LVar retains reduce_lvars=%b behavior" reduce_lvars)
        (if reduce_lvars then Expr.int 7 else variable)
        (Reduction.reduce_lexpr ~reduce_lvars ~pfs:variable_pfs
           ~gamma:variable_gamma variable)) [false;true];
  check "excluded LVar reduction preserves its original contexts"
    (Gamma.to_list variable_gamma = ["#snapshot_variable",Type.IntType]
     && List.equal ( == ) [variable_fact] (P.to_list variable_pfs));
  let nan = Expr.num (Int64.float_of_bits 0x7ff8000000000001L) in
  List.iter (fun (label,expression,expected) ->
      let actual = Reduction.reduce_lexpr expression in
      let original = reference ~matching:false ~pfs:(P.init ())
          ~gamma:(Gamma.copy (Gamma.init ())) expression in
      Alcotest.check expressions label expected actual;
      Alcotest.check expressions (label ^ ": agrees with original snapshot") original actual)
    ["excluded PVar retains its original value",Expr.PVar "snapshot_program",Expr.PVar "snapshot_program";
     "excluded numeric equality retains IEEE signed-zero equality",eq (Expr.num (-0.)) (Expr.num 0.),Expr.true_;
     "excluded NaN equality remains false",eq nan nan,Expr.false_;
     "excluded list expression still normalizes",Expr.EList [Expr.BinOp (Expr.int 2,IPlus,Expr.int 3)],Expr.EList [Expr.int 5];
     "excluded list index still reduces",Expr.BinOp (Expr.EList [Expr.int 2;Expr.int 3],LstNth,Expr.int 1),Expr.int 3;
     "excluded partial right operand remains skipped by false And",Expr.BinOp (Expr.false_,And,partial),Expr.false_;
     "excluded partial right operand remains skipped by true Or",Expr.BinOp (Expr.true_,Or,partial),Expr.true_];
  List.iter (fun (label,expression) ->
      check label (try ignore (Reduction.reduce_lexpr expression); false
        with Reduction.ReductionException _ -> true))
    ["excluded partial root retains its original error",partial;
     "excluded partial right operand remains required by true And",Expr.BinOp (Expr.true_,And,partial);
     "excluded partial right operand remains required by false Or",Expr.BinOp (Expr.false_,Or,partial);
     "excluded number cannot enter Boolean conversion",Expr.UnOp (BoolToInt,Expr.int 1)];
  let list_gamma = Gamma.init () in
  let reference_list_gamma = Gamma.copy list_gamma in
  let list_variable = Expr.LVar "#snapshot_inferred_list" in
  let length_type = Expr.UnOp (TypeOf,Expr.UnOp (LstLen,list_variable)) in
  let total = !Utils.Config.Verification.total in
  Utils.Config.Verification.total := false;
  let actual_length,expected_length = Fun.protect
      ~finally:(fun () -> Utils.Config.Verification.total := total)
      (fun () ->
         compare "legacy closed conjunct membership"
           (Expr.BinOp (positive,And,eq m n)) (positive :: facts);
         Reduction.reduce_lexpr ~gamma:list_gamma length_type,
         reference ~matching:false ~pfs:(P.init ()) ~gamma:reference_list_gamma length_type) in
  Alcotest.check expressions "excluded inferred-list typing agrees with original snapshot"
    expected_length actual_length;
  check "excluded inferred-list typing preserves real gamma inference"
    (Expr.equal actual_length (Expr.Lit (Literal.Type Type.IntType))
     && Gamma.get list_gamma "#snapshot_inferred_list" = Some Type.ListType
     && snapshot list_gamma = snapshot reference_list_gamma);
  let bound = "#snapshot_bound" in
  let binder_gamma = Gamma.init () in
  Gamma.update binder_gamma bound Type.IntType;
  let binder_fact = eq (Expr.LVar bound) (Expr.int 7) in
  let binder_pfs = P.of_list [binder_fact] in
  List.iter (fun universal ->
      let body = eq (Expr.LVar bound) (Expr.int 7) in
      let quantified = if universal then Expr.ForAll ([bound,Some Type.IntType],body)
        else Expr.Exists ([bound,Some Type.IntType],body) in
      let original = reference ~matching:false ~pfs:(P.copy binder_pfs)
          ~gamma:(Gamma.copy binder_gamma) quantified in
      Alcotest.check expressions
        (if universal then "original universal snapshot retains shadowed equality"
         else "original existential snapshot retains shadowed equality") quantified original;
      Alcotest.check expressions
        (if universal then "excluded universal binder retains shadowed equality"
         else "excluded existential binder retains shadowed equality") quantified
        (Reduction.reduce_lexpr ~reduce_lvars:true ~pfs:binder_pfs ~gamma:binder_gamma quantified)) [false;true];
  check "excluded binders preserve outer gamma and original PFS objects"
    (Gamma.to_list binder_gamma = [bound,Type.IntType]
     && List.equal ( == ) [binder_fact] (P.to_list binder_pfs))

let live_guard_membership () =
  let module Reduction = Gillian.Logic.Reduction in
  let module Gamma = Gillian.Symbolic.Type_env in
  let module P = Engine.PFS in
  let check label actual = Alcotest.(check bool) label true actual in
  let expressions = Alcotest.testable (Fmt.Dump.list Expr.pp) (List.equal Expr.equal) in
  let eq a b = Expr.BinOp (a,Equal,b) in
  let snapshot gamma = List.sort
      (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  let original_map ~matching gamma pfs =
    P.map_inplace (Reduction.reduce_lexpr ~matching ~gamma ~pfs) pfs in
  let indexed_map ~matching gamma pfs =
    Reduction.reduce_pfs_in_place ~matching gamma pfs in
  (* The sanitizer is private. Reproduce its exact fixedpoint/dedup skeleton
     with the original public reducer or the actual new internal map pass. *)
  let sanitise pass ~matching gamma pfs =
    let old_pfs = ref (P.init ()) in
    while not (P.equal !old_pfs pfs) do
      old_pfs := P.copy pfs;
      pass ~matching gamma pfs
    done;
    P.remove_duplicates pfs in
  let rec retained_leaves = function
    | (Expr.ALoc _ | Expr.LVar _ | Expr.PVar _
       | Expr.Lit (Literal.Loc _ | Literal.Null | Literal.Num _
                  | Literal.Utf16String _)) as leaf -> [leaf]
    | Expr.UnOp (_,child) | Expr.Exists (_,child) | Expr.ForAll (_,child) ->
        retained_leaves child
    | Expr.BinOp (left,_,right) -> retained_leaves left @ retained_leaves right
    | Expr.EList values -> List.concat_map retained_leaves values
    | _ -> [] in
  let gamma = Gamma.init () in
  List.iteri (fun i typ ->
      Gamma.update gamma (Printf.sprintf "#live_unrelated_%04d" i) typ)
    (List.init 512 (fun i -> match i mod 4 with
         | 0 -> Type.BooleanType | 1 -> Type.ListType
         | 2 -> Type.ObjectType | _ -> Type.NumberType));
  List.iter (fun (name,typ) -> Gamma.update gamma name typ)
    ["#loc_live_a",Type.NumberType; "#loc_live_b",Type.ListType;
     "#live_bound",Type.IntType; "#live_count_a",Type.NumberType;
     "#live_count_z",Type.NumberType];
  let a = Expr.ALoc "#loc_live_a" and b = Expr.ALoc "#loc_live_b" in
  let m = Expr.ALoc "#loc_live_m" and n = Expr.ALoc "#loc_live_n" in
  let q = eq a b and r = eq m n in
  let newly_closed = Expr.BinOp (Expr.true_,Impl,q) in
  let old_closed = Expr.UnOp (Not,Expr.UnOp (Not,q)) in
  let count_a = Expr.LVar "#live_count_a" and count_z = Expr.LVar "#live_count_z" in
  let xs = Expr.LVar "#live_inferred_list" in
  let bound = Expr.LVar "#live_bound" in
  let nan bits = Expr.num (Int64.float_of_bits bits) in
  let nan1 = nan 0x7ff8000000000001L and nan2 = nan 0x7ff8000000000002L in
  let utf units = Expr.Lit (Literal.Utf16String
      (Utils.Utf16.of_canonical (Utils.Utf16.of_code_units units))) in
  let utf1 = utf [0;0xd800] and utf2 = utf [0;0xdc00] in
  let cases =
    ["empty",[];
     "directional untouched suffix",[q;Expr.BinOp (Expr.UnOp (Not,q),Or,r);r];
     "new closed prefix fact",[newly_closed;Expr.BinOp (q,Or,r)];
     "old closed fact replacement",[old_closed;Expr.BinOp (Expr.UnOp (Not,q),Or,r)];
     "duplicate live prefix and suffix",[newly_closed;q;q;Expr.BinOp (q,Or,r)];
     "negative membership",[Expr.UnOp (Not,q);Expr.BinOp (q,And,r);Expr.BinOp (q,Or,r)];
     "mixed closed leaves",[eq a (Expr.Lit Literal.Null);
        eq (Expr.Lit (Literal.Loc "$live")) a;
        Expr.UnOp (Not,eq (Expr.Lit Literal.Null) (Expr.Lit Literal.Null))];
     "fallback inference and numeric snapshot",[
        Expr.UnOp (TypeOf,Expr.UnOp (LstLen,xs));
        Expr.EList [Expr.BinOp (Expr.int 2,IPlus,Expr.int 3);Expr.num (-0.);nan1;utf1];
        Expr.Lit (Literal.Constant Constant.Pi);
        Expr.UnOp (NumToInt,count_z);Expr.UnOp (IsInt,count_z);
        eq count_z count_a;Expr.UnOp (IsInt,count_a)];
     "binder and implication copies",[
        eq bound (Expr.int 7);
        Expr.ForAll (["#live_bound",Some Type.IntType],eq bound (Expr.int 7));
        Expr.Exists (["#live_bound",Some Type.IntType],eq bound (Expr.int 7));
        Expr.BinOp (q,Impl,Expr.BinOp (q,Or,r))];
     "excluded IEEE and UTF16 structural keys",[
        Expr.num 0.;Expr.num (-0.);nan1;nan 0x7ff8000000000001L;nan2;
        utf1;utf [0;0xd800];utf2;eq nan1 nan1;eq (Expr.num (-0.)) (Expr.num 0.)]] in
  List.iter (fun matching ->
      List.iter (fun (phase,original,actual) ->
          List.iter (fun (name,values) ->
              let label suffix = Printf.sprintf "%s matching=%b %s %s"
                  phase matching name suffix in
              let expected_pfs = P.of_list values and actual_pfs = P.of_list values in
              let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
              let source_leaves = List.concat_map retained_leaves values in
              let original_leaves expressions =
                List.concat_map retained_leaves expressions
                |> List.filter (fun leaf -> List.exists (( == ) leaf) source_leaves) in
              original ~matching expected_gamma expected_pfs;
              actual ~matching actual_gamma actual_pfs;
              let expected = P.to_list expected_pfs and actual = P.to_list actual_pfs in
              Alcotest.check expressions (label "agrees with original ordered contents") expected actual;
              check (label "agrees with original gamma effects")
                (snapshot expected_gamma = snapshot actual_gamma);
              check (label "preserves reachable queue length")
                (P.length actual_pfs = List.length actual
                 && P.length expected_pfs = List.length expected
                 && P.length actual_pfs = P.length expected_pfs);
              check (label "retains the same original leaf objects")
                (List.equal ( == ) (original_leaves expected) (original_leaves actual));
              check (label "agrees with live structural membership")
                (List.for_all (fun expression ->
                     P.mem expected_pfs expression = P.mem actual_pfs expression)
                   (values @ [q;r;old_closed;newly_closed;nan1;nan2;utf1;utf2]))) cases)
        ["map",original_map,indexed_map;
         "sanitise",sanitise original_map,sanitise indexed_map]) [false;true];
  let live = P.of_list [newly_closed;Expr.BinOp (q,Or,r)] in
  Reduction.reduce_pfs_in_place ~matching:true (Gamma.copy gamma) live;
  Alcotest.check expressions "new closed prefix fact is visible to the next root"
    [q;Expr.true_] (P.to_list live);
  check "replaced nonclosed old fact is absent from the returned queue"
    (not (P.mem live newly_closed) && P.mem live q);
  let replaced = P.of_list [old_closed;Expr.BinOp (Expr.UnOp (Not,q),Or,r)] in
  Reduction.reduce_pfs_in_place ~matching:true (Gamma.copy gamma) replaced;
  Alcotest.check expressions "old closed fact replacement updates later negative membership"
    [q;r] (P.to_list replaced);
  check "old closed fact leaves the queue after replacement"
    (not (P.mem replaced old_closed) && P.mem replaced q);
  let duplicates = P.of_list [q;q;Expr.BinOp (q,Or,r)] in
  Reduction.reduce_pfs_in_place ~matching:true (Gamma.copy gamma) duplicates;
  Alcotest.check expressions "duplicate occurrences remain visible through the full map"
    [q;q;Expr.true_] (P.to_list duplicates);
  check "map preserves duplicate multiplicity and reachable tail"
    (P.length duplicates = 3 && List.length (P.to_list duplicates) = 3);
  P.extend duplicates r;
  check "mapped duplicate queue remains appendable in original order"
    (P.length duplicates = 4 && List.equal Expr.equal
       [q;q;Expr.true_;r] (P.to_list duplicates));
  let partial = Expr.UnOp (Car,Expr.EList []) in
  let suffix = Expr.BinOp (q,Or,r) in
  let failing = [newly_closed;Expr.UnOp (TypeOf,Expr.UnOp (LstLen,xs));partial;suffix;utf1] in
  let rec drop n values = if n = 0 then values else drop (n - 1) (List.tl values) in
  List.iter (fun matching ->
      let label suffix = Printf.sprintf "first error matching=%b %s" matching suffix in
      let expected_pfs = P.of_list failing and actual_pfs = P.of_list failing in
      let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
      let failure pass gamma pfs =
        try pass ~matching gamma pfs; None
        with Reduction.ReductionException (expression,message) -> Some (expression,message) in
      let expected = failure original_map expected_gamma expected_pfs in
      let actual = failure indexed_map actual_gamma actual_pfs in
      check (label "retains the exact original reduction error")
        (match expected,actual with
         | Some (e,m),Some (e',m') -> Expr.equal e e' && m = m'
         | _ -> false);
      Alcotest.check expressions (label "retains the completed original prefix")
        (P.to_list expected_pfs) (P.to_list actual_pfs);
      check (label "leaves the failing cell and suffix objects untouched")
        (List.equal ( == ) (drop 2 failing) (drop 2 (P.to_list actual_pfs)));
      check (label "retains prior gamma inference and context")
        (snapshot expected_gamma = snapshot actual_gamma
         && Gamma.get actual_gamma "#live_inferred_list" = Some Type.ListType);
      check (label "preserves queue length on failure")
        (P.length actual_pfs = List.length failing)) [false;true];
  List.iter (fun (label,expression) ->
      let expected_pfs = P.of_list [expression] and actual_pfs = P.of_list [expression] in
      let failure pass pfs =
        try pass ~matching:true (Gamma.copy gamma) pfs; false
        with Reduction.ReductionException _ -> true in
      check label (failure original_map expected_pfs
        && failure indexed_map actual_pfs
        && List.equal ( == ) [expression] (P.to_list actual_pfs)))
    ["fallback required right operand preserves its first error",
       Expr.BinOp (Expr.true_,And,partial);
     "fallback invalid Number to Boolean typing still rejects",
       Expr.UnOp (BoolToInt,count_z)];
  List.iter (fun (label,expression,expected) ->
      let pfs = P.of_list [expression] in
      Reduction.reduce_pfs_in_place ~matching:true (Gamma.copy gamma) pfs;
      Alcotest.check expressions label [expected] (P.to_list pfs))
    ["fallback false And still skips the partial right operand",
       Expr.BinOp (Expr.false_,And,partial),Expr.false_;
     "fallback true Or still skips the partial right operand",
       Expr.BinOp (Expr.true_,Or,partial),Expr.true_]

let preparation_lookup_profile () =
  let open BinOp in
  let module R = Gillian.Logic.Reduction in
  let module G = Gillian.Symbolic.Type_env in
  let module P = Engine.PFS in
  let check label actual = Alcotest.(check bool) label true actual in
  let expressions = Alcotest.testable Expr.pp Expr.equal in
  let snapshot gamma = List.sort
      (fun (a,_) (b,_) -> String.compare a b) (G.to_list gamma) in
  let zero (c : R.preparation_profile_counter) =
    c.started = 0 && c.completed = 0 && c.hits = 0 && c.samples = 0 in
  let all_zero (s : R.preparation_profile_snapshot) =
    Array.for_all (Array.for_all zero) s.membership && Array.for_all zero s.copies in
  let counts cells = Array.to_list
      (Array.map (fun (c : R.preparation_profile_counter) -> c.started) cells) in
  let cpu_valid (c : R.preparation_profile_counter) =
    c.cpu_sum >= 0. && c.cpu_max >= 0. && c.cpu_max <= c.cpu_sum
    && c.cpu_zero <= c.samples && Float.is_finite c.cpu_sum in
  let vector sites = List.init 8 (fun i -> if List.mem i sites then 1 else 0) in
  check "profile startup environment enables the selected observer process" R.preparation_profile_enabled;
  R.preparation_profile_reset ();
  check "profile reset starts with empty operation counters" (all_zero (R.preparation_profile_snapshot ()));
  let gamma = G.init () in
  G.update gamma "#profile_x" Type.BooleanType;
  G.update gamma "#profile_y" Type.BooleanType;
  let x = Expr.LVar "#profile_x" and y = Expr.LVar "#profile_y" in
  let cases =
    ["And miss",And,[],[0;1;2;3],[],Expr.BinOp (x,And,y),None;
     "And negative left",And,[Expr.UnOp (Not,x)],[0],[0],Expr.false_,None;
     "And negative right",And,[Expr.UnOp (Not,y)],[0;1],[1],Expr.false_,None;
     "And positive left",And,[x],[0;1;2],[2],y,Some y;
     "And positive right",And,[y],[0;1;2;3],[3],x,Some x;
     "Or miss",Or,[],[4;5;6;7],[],Expr.BinOp (x,Or,y),None;
     "Or positive left",Or,[x],[4],[4],Expr.true_,None;
     "Or positive right",Or,[y],[4;5],[5],Expr.true_,None;
     "Or negative left",Or,[Expr.UnOp (Not,x)],[4;5;6],[6],y,Some y;
     "Or negative right",Or,[Expr.UnOp (Not,y)],[4;5;6;7],[7],x,Some x] in
  List.iter (fun matching -> List.iter
      (fun (name,op,facts,sites,hits,expected,leaf) ->
        let label suffix = Printf.sprintf "profile matching=%b %s %s" matching name suffix in
        R.preparation_profile_reset ();
        let pfs = P.of_list facts and before = snapshot gamma in
        let actual = R.reduce_lexpr ~matching ~pfs ~gamma (Expr.BinOp (x,op,y)) in
        let s = R.preparation_profile_snapshot () in
        Alcotest.check expressions (label "preserves the original result") expected actual;
        check (label "counts exact reached sites returns and hits")
          (counts s.membership.(0) = vector sites
           && Array.to_list (Array.map (fun (c : R.preparation_profile_counter) -> c.completed)
                s.membership.(0)) = vector sites
           && Array.to_list (Array.map (fun (c : R.preparation_profile_counter) -> c.hits)
                s.membership.(0)) = vector hits);
        check (label "does not relabel scan calls as closed index")
          (Array.for_all zero s.membership.(1));
        check (label "records one original generic input copy")
          (counts s.copies = [1;0;0] && s.copies.(0).completed = 1
           && s.copies.(0).size_min = 2 && s.copies.(0).size_max = 2);
        check (label "records metadata sizes and first samples")
          (Array.for_all (fun (c : R.preparation_profile_counter) ->
               c.samples = c.started && cpu_valid c
               && (c.started = 0 || (c.size_min = List.length facts
                                    && c.size_max = List.length facts))) s.membership.(0));
        check (label "preserves original leaf PFS and gamma objects")
          ((match leaf with None -> true | Some leaf -> actual == leaf)
           && List.equal ( == ) facts (P.to_list pfs) && before = snapshot gamma)) cases) [false;true];
  R.preparation_profile_reset ();
  let empty = P.init () in
  let expression = Expr.BinOp (x,And,y) in
  for _ = 1 to 255 do ignore (R.reduce_lexpr ~pfs:empty ~gamma expression) done;
  let s255 = R.preparation_profile_snapshot () in
  check "profile samples first operation before the 256th boundary"
    (s255.copies.(0).started = 255 && s255.copies.(0).samples = 1
     && List.for_all (fun i -> s255.membership.(0).(i).started = 255
          && s255.membership.(0).(i).samples = 1) [0;1;2;3]);
  ignore (R.reduce_lexpr ~pfs:empty ~gamma expression);
  let s256 = R.preparation_profile_snapshot () in
  check "profile samples the literal 256th operation exactly once"
    (s256.copies.(0).started = 256 && s256.copies.(0).samples = 2
     && List.for_all (fun i -> s256.membership.(0).(i).started = 256
          && s256.membership.(0).(i).samples = 2) [0;1;2;3]);
  ignore (R.reduce_lexpr ~pfs:empty ~gamma expression);
  let s257 = R.preparation_profile_snapshot () in
  check "profile 257th operation keeps completed counts without another sample"
    (s257.copies.(0).started = 257 && s257.copies.(0).completed = 257
     && s257.copies.(0).samples = 2
     && List.for_all (fun i -> s257.membership.(0).(i).completed = 257
          && s257.membership.(0).(i).samples = 2) [0;1;2;3]);
  s257.membership.(0).(0) <- s257.membership.(0).(4);
  check "profile snapshot arrays cannot mutate live counters"
    ((R.preparation_profile_snapshot ()).membership.(0).(0).started = 257);
  R.preparation_profile_reset ();
  let eq a b = Expr.BinOp (a,Equal,b) in
  let q = eq (Expr.ALoc "#loc_profile_a") (Expr.ALoc "#loc_profile_b")
  and r = eq (Expr.ALoc "#loc_profile_m") (Expr.ALoc "#loc_profile_n") in
  let public = R.reduce_lexpr ~matching:true ~pfs:empty ~gamma (Expr.BinOp (q,Or,r)) in
  let s = R.preparation_profile_snapshot () in
  check "profile public closed roots still use scans without gamma copies"
    (Expr.equal public (Expr.BinOp (q,Or,r)) && counts s.membership.(0) = vector [4;5;6;7]
     && Array.for_all zero s.membership.(1) && Array.for_all zero s.copies);
  R.preparation_profile_reset ();
  let indexed = P.of_list [Expr.BinOp (Expr.true_,Impl,q);Expr.BinOp (q,Or,r)] in
  R.reduce_pfs_in_place ~matching:true gamma indexed;
  let s = R.preparation_profile_snapshot () in
  check "profile closed index records its live prefix hit and actual backend"
    (List.equal Expr.equal [q;Expr.true_] (P.to_list indexed)
     && Array.for_all zero s.membership.(0) && counts s.membership.(1) = vector [4]
     && s.membership.(1).(4).hits = 1 && s.membership.(1).(4).size_min = 2
     && counts s.copies = [1;0;0]);
  R.preparation_profile_reset ();
  let indexed_miss = P.of_list [Expr.BinOp (q,Or,r)] in
  R.reduce_pfs_in_place ~matching:true gamma indexed_miss;
  let s = R.preparation_profile_snapshot () in
  check "profile closed index misses preserve the ordered query sequence"
    (counts s.membership.(1) = vector [4;5;6;7]
     && Array.for_all (fun (c : R.preparation_profile_counter) -> c.hits = 0) s.membership.(1)
     && Array.for_all zero s.membership.(0) && Array.for_all zero s.copies);
  R.preparation_profile_reset ();
  let nonmatching = P.of_list [Expr.BinOp (q,Or,r)] in
  R.reduce_pfs_in_place ~matching:false gamma nonmatching;
  check "profile retains the nonmatching location reduction and skipped queries"
    (List.equal Expr.equal [Expr.false_] (P.to_list nonmatching)
     && all_zero (R.preparation_profile_snapshot ()));
  R.preparation_profile_reset ();
  let implication = R.reduce_lexpr ~matching:true ~pfs:empty ~gamma
      (Expr.BinOp (q,Impl,Expr.BinOp (q,Or,r))) in
  let s = R.preparation_profile_snapshot () in
  check "profile copied implication queries scan its local extra assumption"
    (Expr.equal implication Expr.true_ && s.membership.(0).(4).hits > 0
     && Array.for_all zero s.membership.(1) && counts s.copies = [1;0;0]
     && P.length empty = 0 && snapshot gamma = ["#profile_x",Type.BooleanType;"#profile_y",Type.BooleanType]);
  List.iter (fun universal ->
      R.preparation_profile_reset ();
      let name = "#profile_bound" in
      let bound = Expr.LVar name and bound_gamma = G.init () in
      G.update bound_gamma name Type.IntType;
      let fact = eq bound (Expr.int 7) in
      let pfs = P.of_list [fact] in
      let quantified = if universal then Expr.ForAll ([name,Some Type.IntType],fact)
        else Expr.Exists ([name,Some Type.IntType],fact) in
      let actual = R.reduce_lexpr ~pfs ~gamma:bound_gamma quantified in
      let s = R.preparation_profile_snapshot () in
      let label suffix = Printf.sprintf "profile quantified universal=%b %s" universal suffix in
      Alcotest.check expressions (label "preserves the shadowed original result") quantified actual;
      check (label "counts all three original copy categories once")
        (counts s.copies = [1;1;1] && Array.for_all (fun (c : R.preparation_profile_counter) ->
             c.completed = 1 && c.samples = 1 && c.size_min = 1 && c.size_max = 1) s.copies);
      check (label "keeps caller gamma and original PFS objects isolated")
        (G.to_list bound_gamma = [name,Type.IntType] && List.equal ( == ) [fact] (P.to_list pfs)
         && Array.for_all zero s.membership.(1))) [false;true];
  let partial = Expr.UnOp (Car,Expr.EList []) in
  List.iter (fun (name,expression,expected) ->
      R.preparation_profile_reset ();
      let before = snapshot gamma in
      let actual = R.reduce_lexpr ~pfs:empty ~gamma expression in
      let s = R.preparation_profile_snapshot () in
      check ("profile " ^ name ^ " preserves skipped partial operand and counters")
        (Expr.equal actual expected && counts s.copies = [1;0;0]
         && Array.for_all (Array.for_all zero) s.membership && before = snapshot gamma))
    ["false And",Expr.BinOp (Expr.false_,And,partial),Expr.false_;
     "true Or",Expr.BinOp (Expr.true_,Or,partial),Expr.true_];
  R.preparation_profile_reset ();
  (match R.reduce_lexpr ~pfs:empty ~gamma (Expr.BinOp (x,And,partial)) with
   | _ -> Alcotest.fail "required partial operand must fail before membership"
   | exception R.ReductionException (failed,message) ->
       let s = R.preparation_profile_snapshot () in
       check "profile required partial operand preserves its exact first error"
         (Expr.equal failed partial && message = "Invalid List Expression"
          && counts s.copies = [1;0;0] && Array.for_all (Array.for_all zero) s.membership
          && P.length empty = 0));
  R.preparation_profile_reset ();
  let bad_gamma = G.init () in
  G.update bad_gamma "#profile_number" Type.NumberType;
  let invalid = Expr.UnOp (BoolToInt,Expr.LVar "#profile_number") in
  (match R.reduce_lexpr ~pfs:empty ~gamma:bad_gamma invalid with
   | _ -> Alcotest.fail "numeric Boolean conversion must reject"
   | exception R.ReductionException (failed,message) ->
       check "profile invalid typing preserves the original error and completed copy"
         (Expr.equal failed invalid && message = "BoolToInt requires a Boolean"
          && counts (R.preparation_profile_snapshot ()).copies = [1;0;0]
          && G.to_list bad_gamma = ["#profile_number",Type.NumberType]));
  R.preparation_profile_dump ();
  let before_final = R.preparation_profile_snapshot () in
  R.preparation_profile_dump ~final:true ();
  let final = R.preparation_profile_snapshot () in
  check "profile dump prepares bounded cumulative metadata and one final report"
    (final.final_report_requested && final.periodic_reports <= 40
     && final.report_payload_bytes > before_final.report_payload_bytes
     && final.report_payload_bytes - before_final.report_payload_bytes <= 8192
     && final.report_payload_bytes <= 524288 && not final.incomplete);
  R.preparation_profile_dump ~final:true ();
  check "profile second forced final report is idempotent"
    ((R.preparation_profile_snapshot ()).report_payload_bytes = final.report_payload_bytes);
  R.preparation_profile_reset ();
  R.preparation_profile_dump ~final:true ();
  let reset = R.preparation_profile_snapshot () in
  check "profile counter reset cannot renew the process reporting budget"
    (all_zero reset && reset.final_report_requested
     && reset.report_payload_bytes = final.report_payload_bytes
     && reset.periodic_reports = final.periodic_reports)

let sanitizer_membership_all () =
  let module Reduction = Gillian.Logic.Reduction in
  let module Gamma = Gillian.Symbolic.Type_env in
  let module P = Engine.PFS in
  let check label actual = Alcotest.(check bool) label true actual in
  let expressions = Alcotest.testable (Fmt.Dump.list Expr.pp) (List.equal Expr.equal) in
  let snapshot gamma = List.sort
      (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  (* The unchanged public reducer is the original ordered-map reference.
     The private sanitizer is represented by its exact fixedpoint/dedup
     skeleton; this is not a direct private-loop or performance oracle. *)
  let original_map ~matching gamma pfs =
    P.map_inplace (Reduction.reduce_lexpr ~matching ~gamma ~pfs) pfs in
  let indexed_map ~matching gamma pfs =
    Reduction.reduce_pfs_in_place ~matching gamma pfs in
  let sanitise pass ~matching gamma pfs =
    let old_pfs = ref (P.init ()) in
    while not (P.equal !old_pfs pfs) do
      old_pfs := P.copy pfs;
      pass ~matching gamma pfs
    done;
    P.remove_duplicates pfs in
  let rec leaves = function
    | (Expr.Lit _ | Expr.LVar _ | Expr.PVar _ | Expr.ALoc _) as leaf -> [leaf]
    | Expr.UnOp (_,child) | Expr.Exists (_,child) | Expr.ForAll (_,child) -> leaves child
    | Expr.BinOp (left,_,right) -> leaves left @ leaves right
    | Expr.EList values -> List.concat_map leaves values
    | _ -> [] in
  let gamma = Gamma.init () in
  List.iteri (fun i typ ->
      Gamma.update gamma (Printf.sprintf "#all_unrelated_%04d" i) typ)
    (List.init 512 (fun i -> match i mod 4 with
         | 0 -> Type.BooleanType | 1 -> Type.ListType
         | 2 -> Type.ObjectType | _ -> Type.NumberType));
  List.iter (fun (name,typ) -> Gamma.update gamma name typ)
    ["#all_number",Type.NumberType; "#all_other_number",Type.NumberType;
     "#all_boolean",Type.BooleanType; "#all_other_boolean",Type.BooleanType;
     "#all_bound",Type.BooleanType; "#all_object",Type.ObjectType];
  let number = Expr.LVar "#all_number" and other = Expr.LVar "#all_other_number" in
  let boolean = Expr.LVar "#all_boolean" and other_boolean = Expr.LVar "#all_other_boolean" in
  let bound = Expr.LVar "#all_bound" and xs = Expr.LVar "#all_inferred_list" in
  let value_equal a b = Expr.BinOp (a,ValueEqual,b) in
  let q = value_equal number (Expr.num 7.) and r = value_equal other (Expr.num 8.) in
  let new_fact = Expr.BinOp (Expr.true_,Impl,q) in
  let old_fact = Expr.UnOp (Not,Expr.UnOp (Not,q)) in
  let object_fact = value_equal (Expr.LVar "#all_object") (Expr.ALoc "#loc_all_object") in
  let nan bits = Expr.num (Int64.float_of_bits bits) in
  let nan1 = nan 0x7ff8000000000001L and nan2 = nan 0x7ff8000000000002L in
  let utf units = Expr.Lit (Literal.Utf16String
      (Utils.Utf16.of_canonical (Utils.Utf16.of_code_units units))) in
  let utf1 = utf [0;0xd800] and utf2 = utf [0;0xdc00] in
  let nq1 = value_equal number nan1 and nq2 = value_equal number nan2 in
  let zq1 = value_equal number (Expr.num 0.) and zq2 = value_equal number (Expr.num (-0.)) in
  let uq1 = value_equal number utf1 and uq2 = value_equal number utf2 in
  let cases =
    ["empty",[];
     "generic ValueEqual suffix",[Expr.BinOp (q,Or,r);q];
     "generic LVar Boolean suffix",[Expr.BinOp (boolean,And,other_boolean);boolean];
     "new generic prefix fact",[new_fact;Expr.BinOp (q,Or,r)];
     "old generic prefix replacement",[old_fact;Expr.BinOp (Expr.UnOp (Not,q),Or,r)];
     "generic duplicate prefix and suffix",[new_fact;q;q;Expr.BinOp (q,Or,r)];
     "generic negative facts",[Expr.UnOp (Not,q);Expr.BinOp (q,And,r);Expr.BinOp (q,Or,r)];
     "object ValueEqual rewrite",[object_fact;Expr.BinOp (object_fact,Or,r)];
     "copied quantified shadow",[bound;
        Expr.ForAll (["#all_bound",Some Type.BooleanType],Expr.BinOp (bound,Or,r));
        Expr.Exists (["#all_bound",Some Type.BooleanType],Expr.BinOp (bound,Or,r))];
     "copied implication assumption",[Expr.BinOp (q,Impl,Expr.BinOp (q,Or,r));other_boolean];
     "inference list and numeric fallback",[Expr.UnOp (TypeOf,Expr.UnOp (LstLen,xs));
        Expr.EList [Expr.BinOp (Expr.int 2,IPlus,Expr.int 3);Expr.num (-0.);nan1;utf1];
        Expr.UnOp (NumToInt,number);Expr.Lit (Literal.Constant Constant.Pi)];
     "exact IEEE UTF16 keys",[nq1;Expr.BinOp (nq2,Or,r);zq1;Expr.BinOp (zq2,Or,r);
        uq1;Expr.BinOp (uq2,Or,r);
        Expr.num 0.;Expr.num (-0.);nan1;nan 0x7ff8000000000001L;nan2;
        utf1;utf [0;0xd800];utf2]] in
  List.iter (fun matching ->
      List.iter (fun (phase,original,actual) ->
          List.iter (fun (name,values) ->
              let label suffix = Printf.sprintf "all facts %s matching=%b %s %s"
                  phase matching name suffix in
              let expected_pfs = P.of_list values and actual_pfs = P.of_list values in
              let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
              let source_leaves = List.concat_map leaves values in
              let retained expressions = List.concat_map leaves expressions
                |> List.filter (fun leaf -> List.exists (( == ) leaf) source_leaves) in
              original ~matching expected_gamma expected_pfs;
              actual ~matching actual_gamma actual_pfs;
              let expected = P.to_list expected_pfs and actual = P.to_list actual_pfs in
              Alcotest.check expressions (label "agrees with original ordered contents") expected actual;
              check (label "agrees with original gamma effects")
                (snapshot expected_gamma = snapshot actual_gamma);
              check (label "preserves reachable queue length and multiplicity")
                (P.length actual_pfs = List.length actual
                 && P.length expected_pfs = List.length expected
                 && P.length actual_pfs = P.length expected_pfs);
              check (label "retains the same original leaf objects")
                (List.equal ( == ) (retained expected) (retained actual));
              check (label "agrees with exact live structural membership")
                (List.for_all (fun expression ->
                     P.mem expected_pfs expression = P.mem actual_pfs expression)
                   (values @ [q;r;old_fact;new_fact;nq1;nq2;zq1;zq2;uq1;uq2;nan1;nan2;utf1;utf2]))) cases)
        ["map",original_map,indexed_map;
         "sanitise",sanitise original_map,sanitise indexed_map]) [false;true];
  List.iter (fun matching ->
      let run values = let pfs = P.of_list values in
        indexed_map ~matching (Gamma.copy gamma) pfs; pfs in
      let label suffix = Printf.sprintf "generic live controls matching=%b %s" matching suffix in
      let live = run [new_fact;Expr.BinOp (q,Or,r)] in
      Alcotest.check expressions (label "new generic fact reaches the next root")
        [q;Expr.true_] (P.to_list live);
      check (label "replaced old fact is absent and new fact is present")
        (not (P.mem live new_fact) && P.mem live q);
      let replaced = run [old_fact;Expr.BinOp (Expr.UnOp (Not,q),Or,r)] in
      Alcotest.check expressions (label "old generic replacement updates negative membership")
        [q;r] (P.to_list replaced);
      let duplicates = run [q;q;Expr.BinOp (q,Or,r)] in
      Alcotest.check expressions (label "duplicate occurrences remain visible")
        [q;q;Expr.true_] (P.to_list duplicates);
      P.extend duplicates other_boolean;
      check (label "duplicate queue retains its appendable tail and first objects")
        (P.length duplicates = 4 && List.equal Expr.equal
           [q;q;Expr.true_;other_boolean] (P.to_list duplicates)
         && List.equal ( == ) [number;number]
              (List.filter (( == ) number) (List.concat_map leaves (P.to_list duplicates))));
      let implication = run [Expr.BinOp (q,Impl,Expr.BinOp (q,Or,r))] in
      Alcotest.check expressions (label "implication uses its copied extra assumption")
        [Expr.true_] (P.to_list implication)) [false;true];
  let partial = Expr.UnOp (Car,Expr.EList []) in
  let failing = [new_fact;Expr.UnOp (TypeOf,Expr.UnOp (LstLen,xs));partial;
                 Expr.BinOp (q,Or,r);utf1] in
  let rec drop n values = if n = 0 then values else drop (n - 1) (List.tl values) in
  List.iter (fun matching ->
      let label suffix = Printf.sprintf "generic first error matching=%b %s" matching suffix in
      let expected_pfs = P.of_list failing and actual_pfs = P.of_list failing in
      let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
      let failure pass gamma pfs = try pass ~matching gamma pfs; None
        with Reduction.ReductionException (expression,message) -> Some (expression,message) in
      let expected = failure original_map expected_gamma expected_pfs in
      let actual = failure indexed_map actual_gamma actual_pfs in
      check (label "retains the exact original reduction error")
        (match expected,actual with
         | Some (e,m),Some (e',m') -> Expr.equal e e' && m = m'
         | _ -> false);
      Alcotest.check expressions (label "retains the completed ordered prefix")
        (P.to_list expected_pfs) (P.to_list actual_pfs);
      check (label "leaves the failing cell and suffix objects untouched")
        (List.equal ( == ) (drop 2 failing) (drop 2 (P.to_list actual_pfs)));
      check (label "retains prior inference and caller context")
        (snapshot expected_gamma = snapshot actual_gamma
         && Gamma.get actual_gamma "#all_inferred_list" = Some Type.ListType);
      check (label "retains reachable length on failure")
        (P.length actual_pfs = List.length failing)) [false;true];
  List.iter (fun matching ->
      List.iter (fun (name,expression,expected) ->
          let label suffix = Printf.sprintf "generic definedness matching=%b %s %s" matching name suffix in
          let expected_pfs = P.of_list [expression] and actual_pfs = P.of_list [expression] in
          let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
          let failure pass gamma pfs = try pass ~matching gamma pfs; None
            with Reduction.ReductionException (expression,message) -> Some (expression,message) in
          let original_failure = failure original_map expected_gamma expected_pfs in
          let actual_failure = failure indexed_map actual_gamma actual_pfs in
          check (label "agrees with original error or skipped operand")
            (match expected,original_failure,actual_failure with
             | None,Some (e,m),Some (e',m') -> Expr.equal e e' && m = m'
             | Some _,None,None -> true
             | _ -> false);
          Alcotest.check expressions (label "retains exact ordered result or failing root")
            (match expected with Some result -> [result] | None -> [expression]) (P.to_list actual_pfs);
          check (label "preserves original context and failed-root identity")
            (snapshot expected_gamma = snapshot actual_gamma
             && (Option.is_some expected || List.equal ( == ) [expression] (P.to_list actual_pfs))))
        ["false And partial",Expr.BinOp (Expr.false_,And,partial),Some Expr.false_;
         "true Or partial",Expr.BinOp (Expr.true_,Or,partial),Some Expr.true_;
         "true And partial",Expr.BinOp (Expr.true_,And,partial),None;
         "false Or partial",Expr.BinOp (Expr.false_,Or,partial),None;
         "invalid numeric Boolean conversion",Expr.UnOp (BoolToInt,number),None]) [false;true];
  (* Controlled fresh map observations only. Output equivalence cannot tell a
     correct old scan from the indexed path; these CPU/allocation observations
     require an actual source-bound run and have no ratio or speed threshold. *)
  List.iter (fun matching -> List.iter (fun size ->
      List.iter (fun mix ->
          let left = Expr.LVar "#all_benchmark_left" and right = Expr.LVar "#all_benchmark_right" in
          let initial_gamma = Gamma.init () in
          Gamma.update initial_gamma "#all_benchmark_left" Type.BooleanType;
          Gamma.update initial_gamma "#all_benchmark_right" Type.BooleanType;
          let fillers = List.init size (fun i -> Expr.string (Printf.sprintf "all_fact_%06d" i)) in
          let queries = List.init 16 (fun _ -> Expr.BinOp (left,Or,right)) in
          let values = queries @ fillers @ (if mix = "suffix-hit" then [left] else []) in
          let expected_pfs = P.of_list values and actual_pfs = P.of_list values in
          let expected_gamma = Gamma.copy initial_gamma and actual_gamma = Gamma.copy initial_gamma in
          let measure pass gamma pfs =
            let allocated = Gc.allocated_bytes () in
            let start = Sys.time () in
            pass ~matching gamma pfs;
            let cpu = Sys.time () -. start in
            cpu,Gc.allocated_bytes () -. allocated in
          let original_cpu,original_allocated = measure original_map expected_gamma expected_pfs in
          let indexed_cpu,indexed_allocated = measure indexed_map actual_gamma actual_pfs in
          let label suffix = Printf.sprintf "all facts benchmark matching=%b size=%d mix=%s %s"
              matching size mix suffix in
          Alcotest.check expressions (label "agrees with original ordered map")
            (P.to_list expected_pfs) (P.to_list actual_pfs);
          check (label "preserves original gamma and reachable length")
            (snapshot expected_gamma = snapshot actual_gamma
             && P.length actual_pfs = List.length values
             && List.length (P.to_list actual_pfs) = List.length values);
          check (label "retains the same filler leaf objects in order")
            (List.equal ( == ) fillers
               (P.to_list actual_pfs |> List.filter (function Expr.Lit (Literal.String _) -> true | _ -> false)));
          Printf.printf "SANITIZER_MEMBERSHIP_BENCHMARK size=%d mix=%s matching=%b original_cpu=%.6f indexed_cpu=%.6f original_allocated_bytes=%.0f indexed_allocated_bytes=%.0f\n%!"
            size mix matching original_cpu indexed_cpu original_allocated indexed_allocated)
        ["absent";"suffix-hit"]) [64;512;2048]) [false;true]

let overlap_guard_append_index () =
  let expressions = Alcotest.testable (Fmt.Dump.list Expr.pp) (List.equal Expr.equal) in
  let module Gamma = Gillian.Symbolic.Type_env in
  let module Reduction = Gillian.Logic.Reduction in
  let module P = Engine.PFS in
  let check label value = Alcotest.(check bool) label true value in
  let snapshot gamma =
    List.sort (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  (* Independent oracle: the unchanged Normaliser classification, public scan
     reducer and ordinary PFS.extend. It never calls the new helper/index. *)
  let original_pass gamma pfs guards =
    List.iter (fun fo ->
      let redundant = match fo with
        | Expr.BinOp
            (Expr.UnOp (Not, Expr.BinOp
               ((Expr.ALoc _ | Expr.Lit (Literal.Loc _)), Equal,
                (Expr.ALoc _ | Expr.Lit (Literal.Loc _)))),
             Or, Expr.BinOp
               (((Expr.ALoc _ | Expr.Lit (Literal.Loc _)
                 | Expr.Lit Literal.Null) as output), Equal, other))
          when Expr.equal output other -> true
        | _ -> try
          let classified = Gamma.copy gamma in
          Reduction.reduce_lexpr ~matching:true ~pfs ~gamma:classified fo = Expr.true_
          && Hashtbl.length (Gamma.as_hashtbl classified)
             = Hashtbl.length (Gamma.as_hashtbl gamma)
          && Gamma.fold classified
               (fun var typ same -> same && Gamma.get gamma var = Some typ) true
        with Reduction.ReductionException _ -> false in
      if not redundant then P.extend pfs fo) guards in
  (* Fatal typing failures propagate from both passes. Compare the error and
     the retained prefix; never turn an invalid Boolean guard into success. *)
  let outcome pass gamma pfs guards =
    try pass gamma pfs guards; None with Failure message -> Some message in
  let run name types facts guards =
    let gamma = Gamma.init () in
    List.iter (fun (x,t) -> Gamma.update gamma x t) types;
    (* Full pass plus every prefix checks live insertion visibility without
       making a reduced result or future guard available prematurely. *)
    List.iter (fun count ->
      let rec take n = function
        | _ when n = 0 -> []
        | x :: xs -> x :: take (n-1) xs
        | [] -> [] in
      let prefix = take count guards in
      let expected = P.of_list facts and actual = P.of_list facts in
      let expected_gamma = Gamma.copy gamma and actual_gamma = Gamma.copy gamma in
      let expected_outcome = outcome original_pass expected_gamma expected prefix in
      let actual_outcome =
        outcome Reduction.extend_pfs_with_overlap_guards actual_gamma actual prefix in
      let label suffix = Printf.sprintf "%s prefix%d %s" name count suffix in
      check (label "same propagated typing failure")
        (expected_outcome = actual_outcome);
      Alcotest.check expressions (label "exact original ordered formulas")
        (P.to_list expected) (P.to_list actual);
      check (label "same original expression objects and duplicate multiplicity")
        (List.equal ( == ) (P.to_list expected) (P.to_list actual));
      check (label "same reachable length") (P.length expected = P.length actual);
      check (label "no speculative typing escape")
        (snapshot gamma = snapshot expected_gamma
         && snapshot expected_gamma = snapshot actual_gamma))
      (List.init (List.length guards + 1) Fun.id) in
  let x = Expr.LVar "#append_x" and y = Expr.LVar "#append_y"
  and bound = Expr.LVar "#append_bound" in
  let booleans = ["#append_x",Type.BooleanType;"#append_y",Type.BooleanType;
    "#append_bound",Type.BooleanType] in
  let or_ left right = Expr.BinOp (left,Or,right) in
  let not_ value = Expr.UnOp (Not,value) in
  run "earlier original insertions are visible" booleans []
    [x; or_ x y; not_ y; or_ x (not_ y)];
  run "future guard is not assumed" booleans [] [or_ x y;x;or_ x y];
  run "pre-existing duplicate objects survive" booleans [x;x;not_ y]
    [x;or_ x y;not_ y;or_ y x];
  run "directional membership" booleans [or_ x y] [or_ y x;or_ x y];
  run "unknown Boolean typing stays quarantined" [] []
    [x;or_ x y;Expr.BinOp (x,Equal,x)];
  let a = Expr.ALoc "#append_a" and b = Expr.ALoc "#append_b"
  and m = Expr.ALoc "#append_m" and n = Expr.ALoc "#append_n" in
  let eq left right = Expr.BinOp (left,Equal,right) in
  let guard i j out other = or_ (not_ (eq i j)) (eq out other) in
  run "closed fast path and retained alias guards" [] []
    [guard a b m m;guard a b m n;guard b a n m;guard a a x x];
  let nan1 = Expr.num (Int64.float_of_bits 0x7ff8000000000001L)
  and nan2 = Expr.num (Int64.float_of_bits 0x7ff8000000000002L) in
  run "signed zero and distinct NaN keys" [] [eq nan1 nan1;eq nan2 nan2]
    [guard a a (Expr.num 0.) (Expr.num (-0.));guard a a nan1 nan1;
     guard a a nan1 nan2;eq nan1 nan1;eq nan2 nan2];
  let partial = Expr.BinOp (Expr.EList [],LstNth,Expr.zero_i) in
  run "partial and skipped Boolean operands" booleans []
    [Expr.BinOp (Expr.false_,And,partial);or_ Expr.true_ partial;
     Expr.BinOp (Expr.true_,And,partial);or_ Expr.false_ partial;
     not_ partial;or_ x partial;Expr.BinOp (Expr.num 1.,And,x);y];
  List.iter (fun universal ->
    let body = or_ bound y in
    let expression = if universal then
        Expr.ForAll (["#append_bound",Some Type.BooleanType],body)
      else Expr.Exists (["#append_bound",Some Type.BooleanType],body) in
    run (if universal then "forall drops outer callback" else "exists drops outer callback")
      booleans [bound] [expression;or_ x expression]) [false;true];
  run "private implication context" booleans []
    [Expr.BinOp (x,Impl,or_ x y);Expr.BinOp (not_ x,Impl,or_ (not_ x) y)];
  (* These explicit non-oracle expectations make the mutation controls binding:
     a stale set retains the second formula, and an always-true set drops x. *)
  let gamma = Gamma.init () in
  List.iter (fun (v,t) -> Gamma.update gamma v t) booleans;
  let pfs = P.init () in
  Reduction.extend_pfs_with_overlap_guards gamma pfs [x;or_ x y];
  Alcotest.check expressions "live append makes later guard redundant" [x] (P.to_list pfs);
  check "original retained object is not a reduced substitute"
    (match P.to_list pfs with [original] -> original == x | _ -> false)

let formula_filter_live_membership () =
  let module Gamma = Gillian.Symbolic.Type_env in
  let module Reduction = Gillian.Logic.Reduction in
  let module P = Engine.PFS in
  let expressions = Alcotest.testable (Fmt.Dump.list Expr.pp) (List.equal Expr.equal) in
  let check label value = Alcotest.(check bool) label true value in
  let snapshot gamma =
    List.sort (fun (a,_) (b,_) -> String.compare a b) (Gamma.to_list gamma) in
  let x = Expr.LVar "#filter_x" and y = Expr.LVar "#filter_y"
  and z = Expr.LVar "#filter_z" and q = Expr.LVar "#filter_q" in
  let probe = Expr.ALoc "#filter_probe" in
  let or_ left right = Expr.BinOp (left,Or,right) in
  let types = List.map (fun name -> name,Type.BooleanType)
      ["#filter_x";"#filter_y";"#filter_z";"#filter_q"] in
  List.iter (fun matching ->
    (* The oracle uses the original public reducer, PFS mutations and queue
       driver. It has no cache, pending-removal or invalidation bookkeeping. *)
    let run name extra_types values script =
      let execute indexed =
        let pfs = P.of_list values and gamma = Gamma.init () in
        List.iter (fun (v,t) -> Gamma.update gamma v t) (types @ extra_types);
        let entries = ref [] and actions = ref [] and queries = ref [] in
        let position = ref 0 in
        let mapper (ops : Reduction.formula_filter_ops) original =
          entries := (original,P.to_list pfs,P.length pfs,snapshot gamma) :: !entries;
          let observed = { ops with reduce_formula = (fun expression ->
            let result = ops.reduce_formula expression in
            queries := (expression,result) :: !queries;
            result) } in
          let n = !position in incr position;
          let action = script n observed original in
          actions := action :: !actions;
          action in
        let outcome = try
          let stopped = if indexed then
              Reduction.filter_map_pfs_with_live_reduction ~matching gamma pfs mapper
            else
              let ops : Reduction.formula_filter_ops = {
                reduce_formula = Reduction.reduce_lexpr ~matching ~pfs ~gamma;
                extend = P.extend pfs;
                substitute = (fun subst -> P.substitution subst pfs);
                substitute_expr = (fun a b -> P.subst_expr_for_expr a b pfs);
              } in
              P.filter_map_stop (mapper ops) pfs in
          `Done stopped
        with
        | Failure message -> `Failure message
        | Reduction.ReductionException (expression,message) ->
            `ReductionError (expression,message) in
        outcome,pfs,snapshot gamma,!entries,!actions,!queries in
      let expected,ep,eg,ee,ea,eq = execute false in
      let actual,ap,ag,ae,aa,aq = execute true in
      let label suffix = Printf.sprintf "filter %s matching=%b %s" name matching suffix in
      let same_outcome = match expected,actual with
        | `Done a,`Done b -> a = b
        | `Failure a,`Failure b -> a = b
        | `ReductionError (e,m),`ReductionError (e',m') -> Expr.equal e e' && m = m'
        | _ -> false in
      check (label "same completion or first propagated error") same_outcome;
      check (label "same callback-entry linked cells, logical length and typing")
        (List.equal (fun (e,fs,n,g) (e',fs',n',g') ->
          Expr.equal e e' && List.equal Expr.equal fs fs' && n=n' && g=g') ee ae);
      check (label "same committed callback actions")
        (List.equal (fun a b -> match a,b with
          | `Filter,`Filter | `Stop,`Stop -> true
          | `Replace e,`Replace e' -> Expr.equal e e'
          | _ -> false) ea aa);
      check (label "same live reductions including recursive mutation lookups")
        (List.equal (fun (e,r) (e',r') -> Expr.equal e e' && Expr.equal r r') eq aq);
      Alcotest.check expressions (label "same final ordered cells and duplicates")
        (P.to_list ep) (P.to_list ap);
      check (label "same logical length and gamma") (P.length ep=P.length ap && eg=ag);
      let retained pfs = P.to_list pfs |> List.filter (fun e ->
          List.exists (( == ) e) values) in
      check (label "same retained original objects")
        (List.equal ( == ) (retained ep) (retained ap));
      actual,ap,aq in
    let keep _ _ original = `Replace original in
    let _,removed,_ = run "delayed filters then unchanged Replace" []
        [x;y;probe;or_ x z] (fun n ops original ->
          if n < 2 then (ignore (ops.reduce_formula (or_ x z)); `Filter)
          else if n=2 then (ignore (ops.reduce_formula (or_ x z)); `Replace original)
          else `Replace (ops.reduce_formula original)) in
    Alcotest.check expressions "unchanged Replace actually unlinks pending facts"
      [probe;or_ x z] (P.to_list removed);
    let _,all_filtered,_ = run "terminal all Filter" [] [x;x;y]
        (fun _ ops _ -> ignore (ops.reduce_formula (or_ x z)); `Filter) in
    check "terminal unlink leaves an empty appendable queue" (P.length all_filtered=0);
    P.extend all_filtered z;
    Alcotest.check expressions "terminal tail supports a subsequent append" [z]
      (P.to_list all_filtered);
    ignore (run "Stop after pending filters" [] [x;probe;y]
      (fun n ops _ -> ignore (ops.reduce_formula (or_ x z)); if n=0 then `Filter else `Stop));
    ignore (run "duplicate fact survives one removal" [] [x;x;or_ x z]
      (fun n ops original -> if n=0 then `Filter
        else `Replace (if n=2 then ops.reduce_formula original else original)));
    let _,appended,_ = run "append at tail then recursive query" [] [probe]
      (fun n ops original -> if n=0 then (
        ignore (ops.reduce_formula (or_ x z)); ops.extend x; ops.extend x;
        ignore (ops.reduce_formula (or_ x z)); `Replace original)
        else `Replace original) in
    Alcotest.check expressions "append uses original deduplication and tail traversal"
      [probe;x] (P.to_list appended);
    List.iter (fun expression_substitution ->
      let _,restored,queries = run
          (if expression_substitution then "expression substitution restores current cell"
           else "whole substitution restores current cell") [] [x;probe;or_ q z]
          (fun n ops original ->
            if n=0 then (
              if expression_substitution then ops.substitute_expr x q
              else ops.substitute (ReturnSubst.init [x,q]);
              ignore (ops.reduce_formula (or_ q z)); `Replace original)
            else `Replace (ops.reduce_formula (if n=1 then or_ q z else original))) in
      Alcotest.check expressions "restored original cannot leave a stale substituted fact"
        [x;or_ q z;or_ q z] (P.to_list restored);
      check "substitution query sees q before restore and misses it afterwards"
        (List.exists (fun (e,r) -> Expr.equal e (or_ q z) && Expr.equal r Expr.true_) queries
         && List.exists (fun (e,r) -> Expr.equal e (or_ q z) && Expr.equal r (or_ q z)) queries))
      [false;true];
    List.iter (fun expression_substitution ->
      ignore (run "substitution while filters pending" [] [y;x;probe;or_ q z]
        (fun n ops original ->
          if n=0 then (ignore (ops.reduce_formula (or_ y z)); `Filter)
          else if n=1 then (
            if expression_substitution then ops.substitute_expr x q
            else ops.substitute (ReturnSubst.init [x,q]);
            ignore (ops.reduce_formula (or_ q z)); `Replace original)
          else `Replace (ops.reduce_formula original)))) [false;true];
    let bound = Expr.LVar "#filter_bound" in
    ignore (run "private quantified and implication contexts"
      ["#filter_bound",Type.BooleanType] [bound;
       Expr.ForAll (["#filter_bound",Some Type.BooleanType],or_ bound z);
       Expr.Exists (["#filter_bound",Some Type.BooleanType],or_ bound z);
       Expr.BinOp (x,Impl,or_ x z)]
      (fun _ ops original -> `Replace (ops.reduce_formula original)));
    let nan bits = Expr.num (Int64.float_of_bits bits) in
    let eq a b = Expr.BinOp (a,ValueEqual,b) in
    let fact = eq (Expr.LVar "#filter_number") (nan 0x7ff8000000000001L) in
    ignore (run "exact NaN and signed-zero structural facts"
      ["#filter_number",Type.NumberType] [fact;fact;or_ fact z;
       or_ (eq (Expr.LVar "#filter_number") (nan 0x7ff8000000000002L)) z;
       eq (Expr.LVar "#filter_number") (Expr.num 0.);
       or_ (eq (Expr.LVar "#filter_number") (Expr.num (-0.))) z]
      (fun _ ops original -> `Replace (ops.reduce_formula original)));
    let _,unchanged,_ = run "no mutation preserves objects" [] [x;x;y;probe] keep in
    check "no-op traversal retains original objects and multiplicity"
      (List.equal ( == ) [x;x;y;probe] (P.to_list unchanged));
    let invalid = Expr.BinOp (Expr.num 1.,And,x) and future = or_ q z in
    let outcome,failed,_ = run "typing failure keeps prior mutation and untouched suffix" []
      [probe;invalid;future]
      (fun n ops original ->
        if n=0 then (ops.extend q; `Replace original)
        else `Replace (ops.reduce_formula original)) in
    check "invalid numeric And propagates a genuine typing failure"
      (match outcome with `Failure _ -> true | _ -> false);
    check "failing cell and future guard are retained, appended fact is not lost"
      (List.equal ( == ) [probe;invalid;future;q] (P.to_list failed)
       && P.length failed=4);
    let partial = Expr.UnOp (Car,Expr.EList []) in
    List.iter (fun expression -> ignore (run "definedness and short-circuit" []
      [probe;expression;or_ q z] (fun _ ops original -> `Replace (ops.reduce_formula original))))
      [partial;Expr.BinOp (Expr.false_,And,partial);or_ Expr.true_ partial;
       Expr.BinOp (Expr.true_,And,partial);or_ Expr.false_ partial]) [false;true];
  (* Exercise the actual recursive Simplifications mapper as well as the
     independent driver. Expected effects retain real substitutions/typing. *)
  let simplify types values =
    let gamma = Gamma.init () and pfs = P.of_list values in
    List.iter (fun (v,t) -> Gamma.update gamma v t) types;
    let subst,remaining = Gillian.Logic.Simplifications.simplify_pfs_and_gamma
      ~matching:true pfs gamma in
    pfs,gamma,subst,remaining in
  let pfs,_,_,_ = simplify types [Expr.BinOp (x,And,y)] in
  check "real mapper expands And into its two original facts"
    (P.length pfs=2 && P.mem pfs x && P.mem pfs y);
  let pfs,_,subst,_ = simplify types [Expr.BinOp (x,Equal,y);or_ x z] in
  check "real alias branch returns a binding and removes the solved equality"
    (ReturnSubst.mem subst x || ReturnSubst.mem subst y);
  check "real alias branch retains a Boolean constraint" (P.length pfs=1);
  let learned = Expr.LVar "#filter_learned" in
  let pfs,gamma,_,_ = simplify []
      [Expr.BinOp (Expr.UnOp (TypeOf,learned),Equal,Expr.Lit (Literal.Type Type.BooleanType))] in
  check "real type-only branch learns gamma and filters its formula"
    (P.length pfs=0 && Gamma.get gamma "#filter_learned"=Some Type.BooleanType);
  let xs = Expr.LVar "#filter_list_x" and ys = Expr.LVar "#filter_list_y" in
  let list_types = ["#filter_list_x",Type.ListType;"#filter_list_y",Type.ListType] in
  let _,_,subst,_ = simplify list_types
    [Expr.BinOp (Expr.NOp (LstCat,[xs;ys]),Equal,Expr.EList [])] in
  check "real empty-concat branch appends and solves both list constraints"
    (ReturnSubst.get subst xs=Some (Expr.EList [])
     && ReturnSubst.get subst ys=Some (Expr.EList []));
  let pfs,_,subst,_ = simplify list_types
    [Expr.BinOp (Expr.LstSub (xs,Expr.int 1,Expr.int 1),Equal,ys)] in
  check "real Sublist branch retains its length constraint and decomposition"
    (P.mem pfs (Expr.BinOp (Expr.UnOp (LstLen,ys),Equal,Expr.int 1))
     && match ReturnSubst.get subst xs with Some (Expr.NOp (LstCat,_)) -> true | _ -> false);
  let a = Expr.ALoc "#filter_protected_a" and b = Expr.ALoc "#filter_protected_b" in
  let protected_error = try
    let gamma = Gamma.init () and pfs = P.of_list [Expr.BinOp (a,Equal,b)] in
    ignore (Gillian.Logic.Simplifications.simplify_pfs_and_gamma ~matching:true
      ~save_spec_vars:(Utils.Containers.SS.of_list
        ["#filter_protected_a";"#filter_protected_b"],false) pfs gamma);
    false
  with Utils.Gillian_result.Exc.Gillian_error
      (Utils.Gillian_result.Error.AnalysisFailures [{msg;_}]) ->
    msg="Cannot merge distinct protected heap locations" in
  check "real protected-location failure is propagated without fallback" protected_error;
  let pfs,_,_,_ = simplify [] [Expr.false_;probe] in
  Alcotest.check expressions "real Stop yields the original false context"
    [Expr.false_] (P.to_list pfs)

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
      ("explicit core input readiness", core_input_readiness);
      ("source precondition guard", with_total_return source_precondition_guard);
      ("source precondition bindings", with_total_return source_precondition_bindings);
      ("source normalization bindings", with_total_return source_normalisation_bindings);
      ("exact summary return", with_total_return exact_return_posts);
      ("numeric summary return", with_total_return numeric_return_posts);
      ("infeasible NaN summary return", with_total_return nan_return_posts);
      ("existing summary return", with_total_return existing_return_posts);
      ("alternative summary returns", with_total_return alternative_return_posts);
      ("sequential recovery preserves frame", with_total_return sequential_recovery);
      ("false sequential recovery rejects", with_total_return false_recovery_goal);
      ("refuted goal needs no recovery", with_total_return refuted_recovery_goal);
      ("conjunctive closure location identity", with_total_return conjunctive_location_identity);
      ("applicable list witnesses", with_total_return applicable_list_witnesses);
      ("partial list witnesses reject", with_total_return partial_list_witnesses);
      ("wrong list shape rejects", with_total_return wrong_list_shape);
      ("overlapping guard normalization", with_total_return overlapping_guard_normalisation);
      ("stable PFS duplicates and queue invariants", stable_pfs_duplicates);
      ("PFS structural identity classes", pfs_structural_identity);
      ("Boolean root reduction and nonliteral controls", with_total_return boolean_root_reduction);
      ("closed-leaf overlap and retained guard controls", with_total_return closed_leaf_overlap);
      ("closed guard snapshot and original reducer controls", with_total_return closed_guard_snapshot);
      ("live guard membership and original map controls", with_total_return live_guard_membership);
      ("preparation lookup observer counters and original effects", with_total_return preparation_lookup_profile);
      ("all-fact sanitizer membership and original map controls", with_total_return sanitizer_membership_all);
      ("append-only overlap classification and original scan controls", with_total_return overlap_guard_append_index);
      ("live formula filter mutations and original scan controls", with_total_return formula_filter_live_membership);
    ]
