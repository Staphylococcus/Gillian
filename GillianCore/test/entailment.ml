open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Config = Gillian.Utils.Config

let bin op a b = Expr.BinOp (a, op, b)
let not_ e = Expr.UnOp (Not, e)
let x = Expr.LVar "#focus_x"
let y = Expr.LVar "#focus_y"
let z = Expr.LVar "#focus_z"

let with_total f () =
  let saved = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := saved) f

let gamma () =
  let g = Gamma.init () in
  List.iter
    (fun name -> Gamma.update g name Type.IntType)
    [ "#focus_x"; "#focus_y"; "#focus_z" ];
  g

let entails facts goal =
  Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
    [ goal ] (gamma ())

let sufficient () =
  let facts = [ bin ILessThan x (Expr.int 0); bin ILessThan (Expr.int 7) z ] in
  Alcotest.(check bool)
    "irrelevant facts do not prevent a sufficient proof" true
    (entails facts (bin ILessThanEqual x (Expr.int 0)));
  Alcotest.(check bool)
    "a false goal still rejects" false
    (entails facts (bin ILessThan x (Expr.int (-2))))

let fallback () =
  (* A goal-local subset retains x < y but omits y <= 0. It has a model for
     x >= 0, whereas the full conjunction has none. SAT must fall back. *)
  let facts = [ bin ILessThan x y; bin ILessThanEqual y (Expr.int 0) ] in
  Alcotest.(check bool)
    "full query proves after inconclusive subset" true
    (entails facts (bin ILessThan x (Expr.int 0)));
  Alcotest.(check bool)
    "full-query counterexample remains a rejection" false
    (entails facts (bin ILessThan x (Expr.int (-1))))

let finite_position () =
  let s = Expr.LVar "#s" and index = Expr.LVar "#index" in
  let pos = Expr.UnOp (ToIntOp, index) in
  let len = Expr.UnOp (IntToNum, Expr.UnOp (Utf16Len, s)) in
  let fs =
    Expr.Set.of_list
      [
        not_ (Expr.UnOp (IsInt, pos));
        not_ (bin FLessThan pos (Expr.num 0.));
        not_ (bin FLessThanEqual len pos);
      ]
  in
  let g = Gamma.init () in
  Gamma.update g "#s" Type.Utf16Type;
  Gamma.update g "#index" Type.NumberType;
  let g = Gamma.as_hashtbl g in
  (* The same native query has a separate constrained resource-control run:
     SMT_TIMEOUT=1 run_tests.exe test 'Sufficient entailment' 2 --json.
     Default runs must prove it, allowing the required full-budget fallback;
     the short-budget run must remain inconclusive
     and the required-query API must still raise its ordinary totality error. *)
  if Sys.getenv_opt "SMT_TIMEOUT" = Some "1" then (
    Alcotest.(check bool)
      "optional unknown cannot prove UNSAT" false (Smt.proves_unsat fs g);
    let rejected check =
      try
        check ();
        false
      with
      | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
        msg = "Incomplete totality proof: SMT returned unknown"
    in
    Alcotest.(check bool)
      "required unknown remains an error" true
      (rejected (fun () -> ignore (Smt.exec_sat fs g)));
    Hashtbl.add g "#other_s" Type.Utf16Type;
    Hashtbl.add g "#other_index" Type.NumberType;
    let seeded_fs =
      Expr.Set.add
        (bin Equal (Expr.LVar "#other_s") s)
        (Expr.Set.add (bin Equal (Expr.LVar "#other_index") index) fs)
    in
    Alcotest.(check bool)
      "seed failure cannot hide required unknown" true
      (rejected (fun () -> ignore (Smt.is_sat seeded_fs g))))
  else
    (* The optional API may legitimately use its bounded unknown outcome.
       A false precheck is not a proof: require actual UNSAT from the original
       query with its full native budget before this control may pass. *)
    let proved = Smt.proves_unsat fs g in
    Alcotest.(check bool)
      "inside ToInteger position is proved by precheck or full query" true
      (proved || Option.is_none (Smt.exec_sat fs g))

let witness_query () =
  let s = Expr.LVar "#witness_s" and i = Expr.LVar "#witness_i" in
  let empty =
    Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical ""))
  in
  let g = Gamma.init () in
  Gamma.update g "#witness_s" Type.Utf16Type;
  Gamma.update g "#witness_i" Type.NumberType;
  Gamma.update g "#witness_other_s" Type.Utf16Type;
  Gamma.update g "#witness_other_i" Type.NumberType;
  let other =
    [
      bin Equal (Expr.LVar "#witness_other_s") empty;
      bin Equal (Expr.LVar "#witness_other_i") (Expr.num 0.);
    ]
  in
  (s, i, empty, g, other)

let seeded_witness () =
  let s, i, empty, g, other = witness_query () in
  let facts =
    [
      bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 0);
      bin Equal i (Expr.num 0.);
    ]
  in
  Alcotest.(check bool)
    "validated full-query witness establishes feasibility" true
    (Smt.is_sat (Expr.Set.of_list (other @ facts)) (Gamma.as_hashtbl g));
  (* A successful witness search must not add its guesses to later proof state. *)
  Alcotest.(check bool)
    "zero index does not force the string to be empty" false
    (Solver.check_entailment Utils.Containers.SS.empty
       (Engine.PFS.of_list [ bin Equal i (Expr.num 0.) ])
       [ bin Equal s empty ]
       g)

let seeded_fallback () =
  let s, i, empty, g, other = witness_query () in
  let different =
    [ not_ (bin Equal s empty); not_ (bin Equal i (Expr.num 0.)) ]
  in
  Alcotest.(check bool)
    "UNSAT seed falls back to a satisfiable full query" true
    (Smt.is_sat (Expr.Set.of_list (other @ different)) (Gamma.as_hashtbl g));
  Alcotest.(check bool)
    "contradictory full query cannot gain a witness" false
    (Smt.is_sat
       (Expr.Set.of_list (other @ (bin Equal s empty :: different)))
       (Gamma.as_hashtbl g))

let tests =
  [
    Alcotest.test_case "sufficient proof and false goal" `Quick
      (with_total sufficient);
    Alcotest.test_case "SAT subset requires full fallback" `Quick
      (with_total fallback);
    Alcotest.test_case "finite-position native precheck" `Quick
      (with_total finite_position);
    Alcotest.test_case "complete-query SAT witness" `Quick
      (with_total seeded_witness);
    Alcotest.test_case "failed SAT seed requires full fallback" `Quick
      (with_total seeded_fallback);
  ]
