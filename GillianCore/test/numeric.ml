open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Reduction = Gillian.Logic.Reduction

let n = Expr.num
let x = Expr.LVar "#numeric_x"
let y = Expr.LVar "#numeric_y"
let bin op a b = Expr.BinOp (a, op, b)
let eq = bin Equal
let neg a = Expr.UnOp (Not, a)

let gamma () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#numeric_x" NumberType;
  Gamma.update gamma "#numeric_y" NumberType;
  gamma

let check_sat label expected fs =
  let gamma = gamma () in
  Alcotest.(check bool)
    (label ^ " (SMT)") expected
    (Smt.is_sat (Expr.Set.of_list fs) (Gamma.as_hashtbl gamma));
  Alcotest.(check bool)
    (label ^ " (simplifier + SMT)")
    expected
    (Solver.check_satisfiability fs gamma)

let rounding () =
  let base = 9007199254740992. in
  let range =
    [ bin FLessThanEqual (n base) x; bin FLessThanEqual x (n (base +. 2.)) ]
  in
  let increment = bin FPlus x (n 1.) in
  check_sat "monotonicity has a counterexample" true
    (neg (bin FLessThan x increment) :: range);
  check_sat "monotonicity also has a satisfying input" true
    (bin FLessThan x increment :: range);
  check_sat "exact rounding" false [ eq x (n base); neg (eq increment x) ];
  check_sat "adding two increases every input in this range" false
    (neg (bin FLessThan x (bin FPlus x (n 2.))) :: range)

let special_values () =
  check_sat "NaN is not reflexive" true [ neg (eq x x) ];
  check_sat "NaN can fail both ordered comparisons" true
    [ neg (bin FLessThan x (n 0.)); neg (bin FLessThanEqual (n 0.) x) ];
  check_sat "numeric equality allows either sign of zero" true
    [ eq x (n 0.); eq (bin FDiv (n 1.) x) (n neg_infinity) ];
  check_sat "overflow" false
    [ eq x (n max_float); neg (eq (bin FTimes x (n 2.)) (n infinity)) ];
  check_sat "underflow" false
    [ eq x (n 5e-324); neg (eq (bin FDiv x (n 2.)) (n 0.)) ]

let untyped_equality () =
  let constraints = [ neg (eq x x) ] in
  Alcotest.(check bool)
    "untyped NaN remains possible" true
    (Solver.check_satisfiability constraints (Gamma.init ()));
  (* The same formula has different results under different typings. *)
  let ints = Hashtbl.create 1 in
  Hashtbl.add ints "#numeric_x" Type.IntType;
  let fs = Expr.Set.of_list constraints in
  Alcotest.(check bool)
    "integer equality is reflexive" false (Smt.is_sat fs ints);
  Alcotest.(check bool)
    "numeric equality is not reflexive" true
    (Smt.is_sat fs (Gamma.as_hashtbl (gamma ())))

let arithmetic_matrix () =
  (* Direct SMT queries ensure concrete reduction cannot mask an encoding bug.
     The expected results come from the same binary64 operations as CExprEval. *)
  let values =
    [
      0.;
      -0.;
      1.;
      -1.;
      0.1;
      5e-324;
      max_float;
      9007199254740992.;
      infinity;
      neg_infinity;
      nan;
    ]
  in
  let ops =
    [
      (BinOp.FPlus, ( +. )); (FMinus, ( -. )); (FTimes, ( *. )); (FDiv, ( /. ));
    ]
  in
  List.iter
    (fun (op, concrete) ->
      List.iter
        (fun a ->
          List.iter
            (fun b ->
              let expected = concrete a b in
              let result = bin op (n a) (n b) in
              let property =
                if Float.is_nan expected then Expr.UnOp (M_isNaN, result)
                else if expected = 0. then
                  eq (bin FDiv (n 1.) result) (n (1. /. expected))
                else eq result (n expected)
              in
              let label = Printf.sprintf "%g %s %g" a (BinOp.str op) b in
              Alcotest.(check bool)
                label false
                (Smt.is_sat
                   (Expr.Set.singleton (neg property))
                   (Hashtbl.create 0)))
            values)
        values)
    ops

let reductions () =
  let check label expr =
    let reduced = Reduction.reduce_lexpr ~gamma:(gamma ()) expr in
    Alcotest.(check bool) label true (Expr.equal expr reduced)
  in
  check "no cancellation" (bin FMinus (bin FPlus x y) y);
  check "no reassociation" (bin FPlus (bin FPlus x (n 1.)) (n 1.));
  check "no distribution through conversion"
    (Expr.UnOp (NumToInt, bin FPlus x y));
  check "no cancellation across rounded integer conversion"
    (Expr.UnOp (NumToInt, Expr.UnOp (IntToNum, Expr.LVar "#integer")));
  check "no floating comparison complement" (neg (bin FLessThan x y));
  Alcotest.(check bool)
    "negate keeps unordered possibility" true
    (Expr.equal (Expr.negate (bin FLessThan x y)) (neg (bin FLessThan x y)));
  Alcotest.(check bool)
    "infix does not cancel" true
    (Expr.equal Expr.Infix.(x +. y -. y) (bin FMinus (bin FPlus x y) y));
  Alcotest.(check bool)
    "infix does not annihilate infinity" true
    (Expr.equal Expr.Infix.(n 0. *. x) (bin FTimes (n 0.) x))

let conversions () =
  let rounded =
    Expr.UnOp (IntToNum, Expr.Lit (Int (Z.of_string "9007199254740993")))
  in
  check_sat "integer conversion rounds" false
    [ neg (eq rounded (n 9007199254740992.)) ];
  let truncated = Expr.UnOp (NumToInt, n (-1.5)) in
  check_sat "negative conversion truncates toward zero" false
    [ neg (eq truncated (Expr.int (-1))) ];
  check_sat "infinity is not an integer" false [ Expr.UnOp (IsInt, n infinity) ];
  List.iter
    (fun operand ->
      Alcotest.check_raises "partial conversion fails closed"
        (Smt.SMT_error
           "SMT encoding: NumToInt requires a finite concrete operand")
        (fun () ->
          ignore
            (Smt.is_sat
               (Expr.Set.singleton
                  (eq (Expr.UnOp (NumToInt, operand)) (Expr.int 0)))
               (Gamma.as_hashtbl (gamma ())))))
    [ x; n nan; n infinity ]

let signed_zero_identity () =
  Alcotest.(check bool)
    "structural equality distinguishes zeros" false
    (Expr.equal (n 0.) (n (-0.)));
  Alcotest.(check int)
    "sets distinguish zeros" 2
    (Expr.Set.cardinal (Expr.Set.of_list [ n 0.; n (-0.) ]));
  let predicate zero = eq (bin FDiv (n 1.) (n zero)) (n infinity) in
  List.iter
    (fun zero ->
      Alcotest.(check bool)
        "cached division keeps sign"
        (1. /. zero > 0.)
        (Smt.is_sat (Expr.Set.singleton (predicate zero)) (Hashtbl.create 0)))
    [ 0.; -0.; 0.; -0. ]

let model () =
  let gamma = gamma () in
  let formulae =
    Expr.Set.of_list
      [
        bin FLessThanEqual (n 9007199254740992.) x;
        bin FLessThanEqual x (n 9007199254740994.);
        neg (bin FLessThan x (bin FPlus x (n 1.)));
      ]
  in
  match Smt.check_sat formulae (Gamma.as_hashtbl gamma) with
  | None -> Alcotest.fail "missing rounding counterexample"
  | Some model -> (
      let lifted = ref None in
      Smt.lift_model model (Gamma.as_hashtbl gamma)
        (fun _ value -> lifted := Some value)
        (Expr.Set.singleton x);
      match !lifted with
      | Some (Expr.Lit (Num value)) ->
          Alcotest.(check bool)
            "counterexample replays in binary64" true
            (value >= 9007199254740992. && value <= 9007199254740994.
            && not (value +. 1. > value))
      | _ -> Alcotest.fail "model did not lift a binary64 value")

let tests =
  [
    ("rounding", `Quick, rounding);
    ("special values", `Quick, special_values);
    ("untyped equality and typed caching", `Quick, untyped_equality);
    ("arithmetic differential matrix", `Quick, arithmetic_matrix);
    ("reductions", `Quick, reductions);
    ("numeric conversions", `Quick, conversions);
    ("signed zero identity and caching", `Quick, signed_zero_identity);
    ("counterexample model", `Quick, model);
  ]
