open Gillian.Gil_syntax
module Reduction = Gillian.Logic.Reduction

let int n = Literal.Int (Z.of_int n)
let list xs = Literal.LList xs
let check label expected actual = Alcotest.(check bool) label expected actual

let literal_identity () =
  let key =
    Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "__proto__")
  in
  List.iter
    (fun (left, right, expected) ->
      List.iter
        (fun (a, b) ->
          check "literal list identity" expected (Literal.equal a b);
          check "expression identity" expected
            (Expr.equal (Expr.Lit a) (Expr.Lit b)))
        [ (left, right); (right, left) ])
    [
      (list [], list [], true);
      (list [ key ], list [], false);
      (list [ int 1 ], list [ int 1; int 2 ], false);
      (list [ int 1; int 2 ], list [ int 2; int 1 ], false);
      (list [ list [] ], list [ list [ int 1 ] ], false);
      (list [ list [ int 1 ] ], list [ list [ int 1 ]; list [] ], false);
      (list [ list [ int 1 ]; list [] ], list [ list [ int 1 ]; list [] ], true);
      (list [ list [ key ] ], list [ list [ key ] ], true);
      (list [], Literal.Null, false);
    ]

let evaluator_agreement () =
  let samples =
    [
      [];
      [ [] ];
      [ [ 1 ] ];
      [ [ 1; 2 ] ];
      [ [ 2; 1 ] ];
      [ []; [ 1 ] ];
      [ [ 1 ]; [] ];
    ]
  in
  let literal xss = list (List.map (fun xs -> list (List.map int xs)) xss) in
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun left ->
      List.iter
        (fun right ->
          let expected = Literal.Bool (left = right) in
          List.iter
            (fun operator ->
              let expression =
                Expr.BinOp
                  (Expr.Lit (literal left), operator, Expr.Lit (literal right))
              in
              check "concrete list comparison" true
                (Literal.equal expected
                   (Engine.CExprEval.evaluate_expr store expression));
              check "reduced list comparison" true
                (Expr.equal (Expr.Lit expected)
                   (Reduction.reduce_lexpr expression)))
            [ BinOp.Equal; BinOp.ValueEqual ])
        samples)
    samples

let filter_guard () =
  let key =
    Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "__proto__")
  in
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun (left, right, expected) ->
      let guard = Expr.BinOp (left, BinOp.Equal, right) in
      check "filter nil guard concrete" true
        (Literal.equal (Literal.Bool expected)
           (Engine.CExprEval.evaluate_expr store guard));
      check "filter nil guard reduction" true
        (Expr.equal (Expr.Lit (Literal.Bool expected))
           (Reduction.reduce_lexpr guard)))
    [
      (Expr.Lit (list [ key ]), Expr.EList [], false);
      (Expr.Lit (list []), Expr.EList [], true);
      (Expr.EList [], Expr.Lit (list [ key ]), false);
    ]

let numeric_identity () =
  let nan1 = Int64.float_of_bits 0x7ff8000000000001L in
  let nan2 = Int64.float_of_bits 0x7ff8000000000002L in
  let nested n = list [ list [ Literal.Num n ] ] in
  check "signed zeros remain distinct" false
    (Literal.equal (nested 0.) (nested (-0.)));
  check "same NaN payload retains structural identity" true
    (Literal.equal (nested nan1) (nested nan1));
  check "different NaN payloads retain structural distinction" false
    (Literal.equal (nested nan1) (nested nan2));
  check "resource same-value still identifies NaNs" true
    (Literal.same_value (nested nan1) (nested nan2));
  check "resource same-value retains signed zeros" false
    (Literal.same_value (nested 0.) (nested (-0.)))

let tests =
  [
    ("literal and expression identity", `Quick, literal_identity);
    ("concrete and reduced comparisons", `Quick, evaluator_agreement);
    ("original filter nil guard", `Quick, filter_guard);
    ("numeric identity distinctions", `Quick, numeric_identity);
  ]
