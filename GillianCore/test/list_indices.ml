open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Reduction = Gillian.Logic.Reduction
module Solver = Gillian.Logic.FOSolver

let check label expected actual = Alcotest.(check bool) label expected actual
let nth xs n = Expr.BinOp (xs, LstNth, Expr.Lit (Int n))
let huge = Z.shift_left Z.one 100
let xs = Expr.LVar "#xs"
let eq a b = Expr.BinOp (a, Equal, b)
let not_ e = Expr.UnOp (Not, e)

let concrete_bounds () =
  let values = [ Literal.Bool true; Literal.Null ] in
  List.iter
    (fun n ->
      let valid = Z.sign n >= 0 && Z.lt n (Z.of_int 2) in
      let concrete = try
          Some (Engine.CExprEval.evaluate_binop
            (Engine.CExprEval.CStore.init []) LstNth
            (Expr.Lit (LList values)) (Expr.Lit (Int n)))
        with Engine.CExprEval.EvaluationError _ -> None in
      let reduced = try Some (Reduction.reduce_lexpr (nth (Expr.Lit (LList values)) n))
        with Reduction.ReductionException _ -> None in
      check "concrete mathematical bound" valid (Option.is_some concrete);
      check "reduced mathematical bound" valid (Option.is_some reduced);
      if valid then
        check "concrete and symbolic element identity" true
          (Expr.equal (Expr.Lit (Option.get concrete)) (Option.get reduced)))
    [ Z.minus_one; Z.zero; Z.one; Z.of_int 2; Z.of_int max_int;
      Z.succ (Z.of_int max_int); huge ]

let abstract_large_index () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#xs" ListType;
  let expression = nth xs huge in
  check "large abstract index is retained exactly" true
    (Expr.equal expression (Reduction.reduce_lexpr ~gamma expression));
  let prefix = Expr.NOp (LstCat, [ Expr.EList [ Expr.bool true ]; xs ]) in
  check "prefix subtraction cannot overflow" true
    (Expr.equal (nth xs (Z.pred huge))
       (Reduction.reduce_lexpr ~gamma (nth prefix huge)))

let slice_offsets () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#xs" ListType;
  let slice = Expr.LstSub (xs, Expr.Lit (Int huge), Expr.int 2) in
  let pfs = Engine.PFS.of_list [ eq xs (Expr.EList [ Expr.bool true ]) ] in
  let rejected = try
      ignore (Reduction.reduce_lexpr ~gamma ~pfs (nth slice Z.one)); false
    with Reduction.ReductionException _ -> true in
  check "slice offset is checked without wrapping" true rejected

let indexed_alias () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#xs" ListType;
  let index = Expr.LVar "#index" in
  let value = Expr.BinOp (xs, LstNth, index) in
  List.iter
    (fun (result, expected) ->
      let facts = [ eq xs (Expr.EList [ Expr.bool true ]);
                    eq index (Expr.int 0); eq value result ] in
      check "raw SMT integer index" expected
        (Smt.is_sat (Expr.Set.of_list facts) (Gamma.as_hashtbl gamma));
      check "reduced integer-index model" expected
        (Solver.check_satisfiability facts gamma))
    [ Expr.bool true, true; Expr.bool false, false ]

let operator_domains () =
  let domains = ref [] in
  let index = Expr.LVar "#index" in
  Engine.Totality.check_expression ~proof:true
    ~require:(fun _ condition -> domains := condition :: !domains)
    ~proves:(fun _ -> false) ~evaluate:Fun.id (Expr.BinOp (xs, LstNth, index));
  let expected = [
    Expr.BinOp (Expr.UnOp (TypeOf, xs), Equal, Expr.Lit (Type ListType));
    Expr.BinOp (Expr.UnOp (TypeOf, index), Equal, Expr.Lit (Type IntType));
    Expr.BinOp (Expr.int 0, ILessThanEqual, index);
    Expr.BinOp (index, ILessThan, Expr.UnOp (LstLen, xs)) ] in
  check "type and exact bounds remain required" true
    (List.for_all (fun condition -> List.exists (fun guarded ->
      match guarded with
      | Expr.BinOp (_, Impl, goal) -> Expr.equal goal condition
      | _ -> false) !domains) expected);
  check "no host-size premise" true (List.length !domains = List.length expected)

let negative_and_noninteger () =
  List.iter
    (fun index ->
      let rejected = try
          ignore (Reduction.reduce_lexpr
            (Expr.BinOp (Expr.EList [ Expr.bool true ], LstNth, index))); false
        with Reduction.ReductionException _ -> true in
      check "invalid index still rejects" true rejected)
    [ Expr.int (-1); Expr.num 0.; Expr.num 0.5; Expr.num nan ]

let tests =
  [ "exact concrete bounds", `Quick, concrete_bounds;
    "large symbolic indices and prefixes", `Quick, abstract_large_index;
    "slice offset overflow rejection", `Quick, slice_offsets;
    "typed and wrapped SMT index aliases", `Quick, indexed_alias;
    "mathematical operator domains", `Quick, operator_domains;
    "negative and noninteger rejection", `Quick, negative_and_noninteger ]
