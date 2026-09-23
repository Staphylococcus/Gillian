open Gillian.Gil_syntax
module Reduction = Gillian.Logic.Reduction
module State = Gillian.Symbolic.SState.Make (Semantics.Symbolic)
module Config = Gillian.Utils.Config
module PState = Gillian.Symbolic.PState.Make (State)
module Totality = Engine.Totality

let bin op a b = Expr.BinOp (a, op, b)
let truth = bin ILessThanEqual (Expr.int 0) (Expr.int 0)
let falsehood = bin ILessThan (Expr.int 0) (Expr.int 0)
let invalid = bin Equal (bin LstNth (Expr.EList []) (Expr.int 0)) (Expr.int 1)

let with_total test () =
  let saved = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := saved) test

let short_circuit () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun term ->
      let concrete = Engine.CExprEval.evaluate_expr store term in
      let reduced = Reduction.reduce_lexpr term in
      Alcotest.(check bool) "matches concrete short circuit" true
        (Expr.equal reduced (Expr.Lit concrete)))
    [ bin Or truth invalid; bin And falsehood invalid;
      Expr.UnOp (Not, bin Or truth invalid);
      Expr.UnOp (Not, bin And falsehood invalid);
      bin And truth (bin Or truth invalid);
      bin Impl truth (bin Or truth invalid);
      bin Impl truth
        (bin Equal (Expr.UnOp (TypeOf, bin Or truth invalid))
           (Expr.Lit (Type BooleanType)));
      bin Impl truth
        (bin Equal (Expr.UnOp (TypeOf, bin And falsehood invalid))
           (Expr.Lit (Type BooleanType))) ]

let required_operand () =
  List.iter
    (fun term ->
      let rejected =
        try ignore (Reduction.reduce_lexpr term); false
        with Reduction.ReductionException _ -> true
      in
      Alcotest.(check bool) "required operand failure propagates" true rejected)
    [ bin Or falsehood invalid; bin And truth invalid;
      bin Or invalid Expr.true_; bin And invalid Expr.false_;
      bin Impl truth invalid ]

let normalization_parents () =
  let store = Engine.CExprEval.CStore.init [] in
  let parents operand =
    [ bin Impl truth
        (bin Equal (Expr.UnOp (LstLen, Expr.EList [ operand ])) (Expr.int 1));
      bin Impl truth (bin Equal operand operand) ]
  in
  List.iter
    (fun (op, required, skipped) ->
      List.iter
        (fun term ->
          let concrete_failed =
            try ignore (Engine.CExprEval.evaluate_expr store term); false with
            | Failure message ->
                (try ignore (Str.search_forward (Str.regexp_string "\nnth\n") message 0); true
                 with Not_found -> false)
          in
          let reduction_failed =
            try ignore (Reduction.reduce_lexpr term); false with
            | Reduction.ReductionException _ -> true
          in
          Alcotest.(check bool) "required operand fails concretely" true concrete_failed;
          Alcotest.(check bool) "parent cannot erase required operand" true reduction_failed)
        (parents (bin op required invalid));
      List.iter
        (fun term ->
          let concrete = Engine.CExprEval.evaluate_expr store term in
          Alcotest.(check bool) "parent preserves skipped operand" true
            (Expr.equal (Reduction.reduce_lexpr term) (Expr.Lit concrete)))
        (parents (bin op skipped invalid)))
    [ (And, truth, falsehood); (Or, falsehood, truth); (Impl, truth, falsehood) ]

let skipped_variable () =
  let state = State.init () in
  let missing = bin Equal (Expr.PVar "missing") (Expr.int 1) in
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun term ->
      let concrete = Engine.CExprEval.evaluate_expr store term in
      Alcotest.(check bool) "skipped variable matches concrete execution" true
        (Expr.equal (State.eval_expr state term) (Expr.Lit concrete)))
    [ bin And falsehood missing; bin Or truth missing; bin Impl falsehood missing;
      Expr.UnOp (Not, bin And falsehood missing) ];
  List.iter
    (fun term ->
      let failed =
        try ignore (State.eval_expr state term); false with
        | State.Internal_State_Error ([ EVar "missing" ], _) -> true
      in
      Alcotest.(check bool) "required variable is still read" true failed)
    [ bin And truth missing; bin Or falsehood missing; bin Impl truth missing;
      bin And missing Expr.false_; bin Or missing Expr.true_ ]

let path_guarded_variable () =
  let n = Expr.LVar "#n" in
  let state = Option.get (State.assume_t (State.init ()) n Type.IntType) in
  let state = Option.get (State.assume_a state [ bin ILessThanEqual (Expr.int 2) n ]) in
  let left = bin ILessThan n (Expr.int 1) in
  let right = bin Equal (Expr.PVar "missing") (Expr.int 1) in
  Alcotest.(check bool) "path facts skip an uninitialized variable" true
    (Expr.equal (State.eval_expr state (bin And left right)) Expr.false_)

let failed_assumption () =
  let state = State.init () in
  let failed =
    try ignore (State.assume_a state [ invalid ]); false
    with
    | Gillian.Utils.Gillian_result.Exc.Gillian_error (AnalysisFailures [ failure ]) ->
        String.starts_with ~prefix:"Proof assumption reduction failed:" failure.msg
  in
  Alcotest.(check bool) "reduction failure is not infeasibility" true failed

let infeasible_assumption () =
  Alcotest.(check bool) "false still prunes an infeasible branch" true
    (Option.is_none (State.assume_a (State.init ()) [ Expr.false_ ]));
  Alcotest.(check bool) "true preserves a feasible branch" true
    (Option.is_some (State.assume_a (State.init ()) [ Expr.true_ ]))

let expect_domain_failure prefix f =
  let failed =
    try f (); false with
    | Gillian.Utils.Gillian_result.Exc.Gillian_error (AnalysisFailures [ failure ]) ->
        String.starts_with ~prefix failure.msg
  in
  Alcotest.(check bool) "intended definedness failure" true failed

let proof_domain () =
  let xs = Expr.LVar "#xs" in
  let state = Option.get (State.assume_t (State.init ()) xs Type.ListType) in
  let check expr =
    Totality.check_proof_expression ~context:"Test proof term"
      ~evaluate:(fun condition ->
        try State.eval_expr state condition with exn ->
          Alcotest.failf "Domain evaluation failed for %a: %s" Expr.pp condition
            (Printexc.to_string exn))
      ~assertion:(fun condition -> State.assert_a state [ condition ]) expr
  in
  check xs;
  check (Expr.ALoc "_$l_test");
  (* Reduction would erase this slice, including its unchecked start offset. *)
  expect_domain_failure "Test proof term is not proved defined:"
    (fun () -> check (Expr.UnOp (LstLen, Expr.LstSub (xs, Expr.int 1, Expr.int 0))));
  check (bin Or truth invalid);
  check (bin And falsehood invalid);
  check (Expr.UnOp (Not, bin Or truth invalid));
  check (Expr.UnOp (Not, bin And falsehood invalid));
  check (bin And (bin ILessThan (Expr.int 0) (Expr.UnOp (LstLen, xs)))
           (bin Equal (bin LstNth xs (Expr.int 0)) (Expr.int 7)))

let executable_leaves () =
  List.iter
    (fun expr ->
      let rejected =
        try
          Totality.check_expression ~require:(fun _ _ -> ())
            ~proves:(fun _ -> false) ~evaluate:Fun.id expr;
          false
        with
        | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
            String.ends_with ~suffix:"logical-only expressions in executable code." msg
      in
      Alcotest.(check bool) "logical leaf stays forbidden in executable syntax"
        true rejected)
    [ Expr.LVar "#xs"; Expr.ALoc "_$l_test" ]

let loop_revisit valid =
  (* Exercise the reuse boundary directly, independently of entry checks. The
     invariant admits both lists; only the supplied measure needs nonemptiness. *)
  let source = Prog.create () in
  let prog = Engine.MP.init_prog { source with procs = Hashtbl.create 1 } in
  let xs = Expr.EList (if valid then [ Expr.int 7 ] else []) in
  let state = PState.set_store (PState.init ())
      (Gillian.Symbolic.Store.init [ ("xs", xs) ]) in
  let variable = Expr.PVar "xs" in
  let rank = Expr.UnOp (LstLen, Expr.LstSub (variable, Expr.int 1, Expr.int 0)) in
  let run () =
    PState.match_invariant prog true state [ Asrt.Types [ (variable, Type.ListType) ] ] []
      ~measure:(Some (rank, Some (Type.IntType, Expr.int 1)))
  in
  if valid then
    Alcotest.(check bool) "valid back-edge measure is preserved" true
      (match run () with [ Ok _ ] -> true | _ -> false)
  else expect_domain_failure "Loop revisit variant is not proved defined:"
      (fun () -> ignore (run ()))

let () =
  Alcotest.run "Proof terms"
    [ ("total mode",
       [ Alcotest.test_case "short circuit" `Quick (with_total short_circuit);
         Alcotest.test_case "required operand" `Quick (with_total required_operand);
         Alcotest.test_case "normalization below erasing parents" `Quick (with_total normalization_parents);
         Alcotest.test_case "short-circuit variable substitution" `Quick (with_total skipped_variable);
         Alcotest.test_case "path-guarded variable substitution" `Quick (with_total path_guarded_variable);
         Alcotest.test_case "failed assumption" `Quick (with_total failed_assumption);
         Alcotest.test_case "infeasible assumption" `Quick (with_total infeasible_assumption);
         Alcotest.test_case "proof domains and guarded operands" `Quick (with_total proof_domain);
         Alcotest.test_case "executable leaf restrictions" `Quick (with_total executable_leaves);
         Alcotest.test_case "invalid loop revisit measure" `Quick (with_total (fun () -> loop_revisit false));
         Alcotest.test_case "valid loop revisit measure" `Quick (with_total (fun () -> loop_revisit true)) ]) ]
