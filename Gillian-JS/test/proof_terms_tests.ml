open Gillian.Gil_syntax
module Reduction = Gillian.Logic.Reduction
module State = Gillian.Symbolic.SState.Make (Semantics.Symbolic)
module Config = Gillian.Utils.Config

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
      Expr.UnOp (Not, bin Or truth invalid) ]

let required_operand () =
  List.iter
    (fun term ->
      let rejected =
        try ignore (Reduction.reduce_lexpr term); false
        with Reduction.ReductionException _ -> true
      in
      Alcotest.(check bool) "required operand failure propagates" true rejected)
    [ bin Or falsehood invalid; bin And truth invalid;
      bin Or invalid Expr.true_; bin And invalid Expr.false_ ]

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

let () =
  Alcotest.run "Proof terms"
    [ ("total mode",
       [ Alcotest.test_case "short circuit" `Quick (with_total short_circuit);
         Alcotest.test_case "required operand" `Quick (with_total required_operand);
         Alcotest.test_case "failed assumption" `Quick (with_total failed_assumption);
         Alcotest.test_case "infeasible assumption" `Quick (with_total infeasible_assumption) ]) ]
