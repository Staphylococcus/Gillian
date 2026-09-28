open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Reduction = Gillian.Logic.Reduction
module Typing = Engine.Typing
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let indicator e = Expr.UnOp (BoolToInt, e)
let eq a b = Expr.BinOp (a, Equal, b)
let not_ e = Expr.UnOp (Not, e)
let check label expected actual = Alcotest.(check bool) label expected actual

let concrete_and_reduction () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun (value, expected) ->
      let expression = indicator (Expr.bool value) in
      check "exact concrete integer" true
        (Literal.equal
           (Literal.Int (Z.of_int expected))
           (Engine.CExprEval.evaluate_expr store expression));
      check "exact reduced integer" true
        (Expr.equal (Expr.int expected) (Reduction.reduce_lexpr expression));
      let printed = Format.asprintf "%a" Expr.pp expression in
      match Parser.parse_expression (Lexing.from_string printed) with
      | Ok recovered ->
          check "GIL roundtrip" true (Expr.equal expression recovered)
      | Error _ -> failwith "Boolean indicator did not parse")
    [ (false, 0); (true, 1) ]

let reject_non_boolean () =
  List.iter
    (fun literal ->
      let expression = indicator (Expr.Lit literal) in
      let concrete_rejected =
        try
          ignore (Engine.CExprEval.evaluate_unop BoolToInt literal);
          false
        with Engine.CExprEval.TypeError _ -> true
      in
      check "concrete non-Boolean rejected" true concrete_rejected;
      let reduced_rejected =
        try
          ignore (Reduction.reduce_lexpr expression);
          false
        with Reduction.ReductionException _ -> true
      in
      check "reduced non-Boolean rejected" true reduced_rejected;
      let _, typable = Typing.type_lexpr (Gamma.init ()) expression in
      check "non-Boolean does not typecheck" false typable)
    [
      Literal.Int Z.zero;
      Num 0.;
      Num 1.;
      Null;
      Undefined;
      String "true";
      LList [];
    ];
  let gamma = Gamma.init () in
  Gamma.update gamma "#bad" NumberType;
  let rejected =
    try
      ignore (Reduction.reduce_lexpr ~gamma (indicator (Expr.LVar "#bad")));
      false
    with Reduction.ReductionException _ -> true
  in
  check "symbolic non-Boolean rejected" true rejected

let check_sat gamma label expected facts =
  check (label ^ " raw SMT") expected
    (Smt.is_sat (Expr.Set.of_list facts) (Gamma.as_hashtbl gamma));
  check
    (label ^ " reduction and SMT")
    expected
    (Solver.check_satisfiability facts gamma)

let symbolic_boolean () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#flag" BooleanType;
  let flag = Expr.LVar "#flag" in
  let value = indicator flag in
  List.iter
    (fun (fact, expected, opposite) ->
      check_sat gamma "required value has model" true
        [ fact; eq value (Expr.int expected) ];
      check_sat gamma "opposite value excluded" false
        [ fact; eq value (Expr.int opposite) ])
    [ (flag, 1, 0); (not_ flag, 0, 1) ];
  check_sat gamma "only zero or one" false
    [ not_ (eq value (Expr.int 0)); not_ (eq value (Expr.int 1)) ];
  check_sat gamma "complement" false
    [
      not_ (eq (Expr.BinOp (value, IPlus, indicator (not_ flag))) (Expr.int 1));
    ];
  let inferred, typable = Typing.type_lexpr gamma value in
  check "integer output type" true (typable && inferred = Some IntType)

let object_identity_rank () =
  let gamma = Gamma.init () in
  List.iter
    (fun n -> Gamma.update gamma n ObjectType)
    [ "#l"; "#base"; "#proto" ];
  let l = Expr.LVar "#l"
  and base = Expr.LVar "#base"
  and proto = Expr.LVar "#proto" in
  let rank value = indicator (eq value base) in
  let entry = eq l base and different = not_ (eq proto base) in
  let descends = Expr.BinOp (rank proto, ILessThan, rank l) in
  check_sat gamma "one-hop inputs satisfiable" true [ entry; different ];
  check_sat gamma "one-hop strict decrease" false
    [ entry; different; not_ descends ];
  check_sat gamma "alias cannot fake descent" false [ eq proto base; descends ];
  check_sat gamma "no-progress cannot descend" false
    [ Expr.BinOp (rank l, ILessThan, rank l) ];
  check_sat gamma "rank natural" false
    [ Expr.BinOp (rank l, ILessThan, Expr.int 0) ]

let tests =
  [
    ("concrete reduction and GIL roundtrip", `Quick, concrete_and_reduction);
    ("non-Boolean rejection", `Quick, reject_non_boolean);
    ("symbolic Boolean exactness", `Quick, symbolic_boolean);
    ("object identity rank descent", `Quick, object_identity_rank);
  ]
