open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Typing = Engine.Typing
module Reduction = Gillian.Logic.Reduction
module Solver = Gillian.Logic.FOSolver

let check label expected actual = Alcotest.(check bool) label expected actual
let head xs = Expr.UnOp (Car, xs)
let eq a b = Expr.BinOp (a, Equal, b)
let not_ e = Expr.UnOp (Not, e)
let key = Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "payload"))

let abstract_head () =
  List.iter
    (fun typed ->
      let gamma = Gamma.init () in
      if typed then Gamma.update gamma "#xs" ListType;
      let xs = Expr.LVar "#xs" in
      let result, typable = Typing.type_lexpr gamma (head xs) in
      check "unknown head type is not invented" true (typable && result = None);
      check "operand remains a list" true (Gamma.get gamma "#xs" = Some ListType);
      let result, typable = Typing.type_lexpr gamma (Expr.UnOp (Cdr, xs)) in
      check "tail remains a list" true (typable && result = Some ListType))
    [ false; true ]

let concrete_heads () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun literal ->
      List.iter
        (fun xs ->
          let expression = head xs in
          let result, typable = Typing.type_lexpr (Gamma.init ()) expression in
          check "known element type" true
            (typable && result = Some (Literal.type_of literal));
          check "concrete evaluator returns the element" true
            (Literal.equal literal (Engine.CExprEval.evaluate_expr store expression));
          check "reduction returns the element" true
            (Expr.equal (Reduction.reduce_lexpr (Expr.Lit literal))
               (Reduction.reduce_lexpr expression)))
        [ Expr.EList [ Expr.Lit literal ]; Expr.Lit (LList [ literal ]) ])
    [ Null; Undefined; Bool false; Bool true; Num 0.; Num (-0.); Num 2.;
      Int Z.zero; String "payload"; Utf16String (Gillian.Utils.Utf16.of_canonical "payload");
      Loc "$head"; LList []; LList [ Null ] ]

let reject_nonlists () =
  List.iter
    (fun value ->
      let _, typable = Typing.type_lexpr (Gamma.init ()) (head value) in
      check "non-list operand rejected" false typable)
    [ Expr.Lit Null; Expr.bool true; Expr.Lit (Num 1.); key ];
  let gamma = Gamma.init () in
  Gamma.update gamma "#bad" NumberType;
  let _, typable = Typing.type_lexpr gamma (head (Expr.LVar "#bad")) in
  check "known symbolic non-list rejected" false typable

let symbolic_branches () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#xs" ListType;
  let xs = Expr.LVar "#xs" in
  let guard = eq (head xs) key in
  let reduced = Reduction.reduce_lexpr ~gamma guard in
  check "match branch is retained" false (Expr.equal reduced Expr.false_);
  check "non-match branch is retained" false (Expr.equal reduced Expr.true_);
  List.iter
    (fun (first, matches) ->
      let facts = [ eq xs (Expr.EList [ first ]); guard ] in
      let opposite = [ eq xs (Expr.EList [ first ]); not_ guard ] in
      List.iter
        (fun (facts, expected) ->
          check "raw SMT branch" expected
            (Smt.is_sat (Expr.Set.of_list facts) (Gamma.as_hashtbl gamma));
          check "reduced SMT branch" expected
            (Solver.check_satisfiability facts gamma))
        [ facts, matches; opposite, not matches ])
    [ key, true; Expr.Lit Null, false; Expr.EList [], false ]

let unknown_list_element () =
  let gamma = Gamma.init () in
  let value = Expr.LVar "#value" in
  let result, typable = Typing.type_lexpr gamma (head (Expr.EList [ value ])) in
  check "untyped explicit head remains unknown" true (typable && result = None);
  check "element acquires no container type" true (Gamma.get gamma "#value" = None)

let partial_domains () =
  let require _ condition =
    if not (Expr.equal (Reduction.reduce_lexpr condition) Expr.true_) then
      failwith "unproved list-head domain"
  in
  let domain expression =
    Engine.Totality.check_expression ~proof:true ~require
      ~proves:(fun e -> Expr.equal (Reduction.reduce_lexpr e) Expr.true_)
      ~evaluate:Fun.id expression
  in
  List.iter
    (fun op ->
      List.iter
        (fun xs ->
          let rejected = try domain (Expr.UnOp (op, xs)); false with
            | Failure message when message = "unproved list-head domain" -> true
          in
          check "empty list remains partial" true rejected)
        [ Expr.EList []; Expr.Lit (LList []) ];
      domain (Expr.UnOp (op, Expr.EList [ key ])))
    [ Car; Cdr ]

let tests =
  [ "abstract head and tail types", `Quick, abstract_head;
    "concrete element types and evaluation", `Quick, concrete_heads;
    "non-list operand rejection", `Quick, reject_nonlists;
    "symbolic key branches", `Quick, symbolic_branches;
    "untyped explicit element", `Quick, unknown_list_element;
    "empty-list totality domains", `Quick, partial_domains ]
