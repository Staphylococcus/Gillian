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

(* Exact descriptor projection must not depend on a Number-only old value. *)
let value_descriptor = Expr.LVar "#value_descriptor"
let program_descriptor = Expr.PVar "value_descriptor"
let value_equal a b = Expr.BinOp (a, ValueEqual, b)
let reduce_value_list facts expression =
  let gamma = Gamma.init () in
  List.iter (fun name -> Gamma.update gamma name ListType)
    [ "#value_descriptor"; "value_descriptor"; "#value_alias" ];
  Reduction.reduce_lexpr ~gamma ~pfs:(Engine.PFS.of_list facts) expression

let value_identity_projection () =
  let old_values =
    [ Expr.LVar "#unconstrained_old"; Expr.PVar "old_value";
      Expr.ALoc "#existing_heap"; Expr.Lit Literal.Null;
      Expr.Lit Literal.Undefined; Expr.bool false ] in
  List.iter (fun variable ->
    List.iter (fun old ->
      let descriptor = Expr.EList
          [ Expr.string "d"; old; Expr.bool true; Expr.bool true; Expr.bool true ] in
      List.iter (fun fact ->
        let reduce = reduce_value_list [ fact ] in
        check "exact identity projects arbitrary prior referent" true
          (Expr.equal old (reduce (nth variable Z.one)));
        check "descriptor writable flag reduces to Boolean true" true
          (Expr.equal Expr.true_ (reduce (nth variable (Z.of_int 2))));
        check "negated writable flag reduces to Boolean false" true
          (Expr.equal Expr.false_ (reduce (not_ (nth variable (Z.of_int 2))))))
        [ value_equal variable descriptor; value_equal descriptor variable ])
      old_values)
    [ value_descriptor; program_descriptor ]

let value_identity_number_bits () =
  (* Compare payloads, not OCaml/JS numeric equality: neither zero sign nor
     the retained NaN bits may be lost by selecting a list component. *)
  List.iter (fun bits ->
    let number = Expr.num (Int64.float_of_bits bits) in
    List.iter (fun variable ->
      List.iter (fun fact ->
        let result = reduce_value_list [ fact ] (nth variable Z.zero) in
        check "exact component retains binary64 payload" true
          (match result with
          | Expr.Lit (Literal.Num n) -> Int64.equal bits (Int64.bits_of_float n)
          | _ -> false))
        [ value_equal variable (Expr.EList [ number ]);
          value_equal (Expr.EList [ number ]) variable ])
      [ value_descriptor; program_descriptor ])
    [ 0x0000000000000000L; 0x8000000000000000L;
      0x7ff8000000000000L; 0x7ff8000000000042L ]

let value_identity_fallbacks () =
  let alias = Expr.LVar "#value_alias" in
  List.iter (fun variable ->
    let expression = nth variable Z.zero in
    List.iter (fun facts ->
      check "unknown/alias/cyclic identities remain unresolved" true
        (Expr.equal expression (reduce_value_list facts expression)))
      [ []; [ value_equal variable alias ];
        [ value_equal variable alias; value_equal alias variable ];
        [ value_equal variable (Expr.EList [ variable ]) ];
        [ value_equal (Expr.EList [ variable ]) variable ];
        [ value_equal variable (Expr.EList [ nth variable Z.zero ]) ];
        [ value_equal variable alias;
          value_equal alias (Expr.EList [ Expr.bool true ]) ] ];
    let one = value_equal variable (Expr.EList [ Expr.bool true ]) in
    List.iter (fun index ->
      check "finite identity still rejects invalid/oversized indices" true
        (try ignore (reduce_value_list [ one ] (nth variable index)); false
         with Reduction.ReductionException _ -> true))
      [ Z.minus_one; Z.one; huge ];
    check "empty finite identity still rejects index zero" true
      (try ignore (reduce_value_list
          [ value_equal variable (Expr.EList []) ] expression); false
       with Reduction.ReductionException _ -> true))
    [ value_descriptor; program_descriptor ];
  check "legacy logical Equal list resolution is preserved" true
    (Expr.equal Expr.true_ (reduce_value_list
      [ eq value_descriptor (Expr.EList [ Expr.bool true ]) ]
      (nth value_descriptor Z.zero)))

(* None is the absent-cell sentinel, not null, undefined or a descriptor. A
   projection exposing an unknown referent must not prove that cell present. *)
let none_projection_equality () =
  let none = Expr.Lit Literal.Nono in
  let project value =
    nth (Expr.EList [ Expr.string "object"; Expr.string "errors"; value ])
      (Z.of_int 2)
  in
  let expressions op value =
    let compare a b = Expr.BinOp (a, op, b) in
    [ compare none value; compare value none;
      compare none (project value); compare (project value) none ]
  in
  let pending label gamma facts op value =
    List.iter (fun expression ->
      let reduced = Reduction.reduce_lexpr ~gamma
          ~pfs:(Engine.PFS.of_list facts) expression in
      check label true
        (match reduced with
         | Expr.BinOp (Expr.Lit Literal.Nono, operation, result) ->
             operation = op && Expr.equal result value
         | Expr.BinOp (result, operation, Expr.Lit Literal.Nono) ->
             operation = op && Expr.equal result value
         | _ -> false))
      (expressions op value)
  in
  let boolean label gamma expected value =
    List.iter (fun expression ->
      check label true (Expr.equal (Expr.bool expected)
        (Reduction.reduce_lexpr ~gamma expression)))
      (expressions Equal value)
  in
  let gamma = Gamma.init () in
  let old = Expr.LVar "#none_old" in
  let program_old = Expr.PVar "none_old" in
  List.iter (fun value ->
    pending "direct/projected unknown None equality stays symbolic"
      gamma [] Equal value;
    pending "ValueEqual identity is not replaced by numeric equality"
      gamma [] ValueEqual value)
    [ old; program_old ];
  let typed_none = Expr.LVar "#typed_none" in
  Gamma.update gamma "#typed_none" NoneType;
  pending "typed None remains a possible absent cell"
    gamma [] Equal typed_none;
  Gamma.update gamma "none_old" NumberType;
  pending "legacy direct/projected PVar handling is preserved"
    gamma [] Equal program_old;
  List.iter (fun typ ->
    let typed = Gamma.init () in
    Gamma.update typed "#none_old" typ;
    boolean "known disjoint logical-variable type rejects None"
      typed false old)
    [ BooleanType; NumberType; ListType; ObjectType ];
  boolean "actual absent literal remains absent" gamma true none;
  List.iter (boolean "present values are distinct from absence" gamma false)
    [ Expr.Lit Literal.Null; Expr.Lit Literal.Undefined;
      Expr.bool false; Expr.ALoc "#prior_object"; Expr.EList [];
      Expr.EList [ Expr.string "d"; old; Expr.bool true ];
      Expr.EList [ Expr.string "d"; Expr.Lit Literal.Null; Expr.bool true ];
      Expr.EList [ Expr.string "d"; Expr.Lit Literal.Undefined; Expr.bool true ] ];
  let cells = Expr.LVar "#none_cells" in
  Gamma.update gamma "#none_cells" ListType;
  let facts =
    [ value_equal cells
        (Expr.EList [ Expr.string "object"; Expr.string "errors"; old ]);
      value_equal old none ]
  in
  List.iter (fun expression ->
    let reduced = Reduction.reduce_lexpr ~gamma
        ~pfs:(Engine.PFS.of_list facts) expression in
    check "actual GetCell projection retains the unknown absence test" true
      (Expr.equal (eq none old) reduced))
    [ eq none (nth cells (Z.of_int 2));
      eq (nth cells (Z.of_int 2)) none ];
  pending "unresolved list projection is not classified present"
    gamma [] Equal (nth cells Z.zero);
  let invalid = nth (Expr.EList []) Z.zero in
  List.iter (fun expression ->
    check "None equality does not swallow invalid projection" true
      (try ignore (Reduction.reduce_lexpr ~gamma expression); false
       with Reduction.ReductionException _ -> true))
    [ eq none invalid; eq invalid none ];
  let probe = Expr.LVar "#none_boolean_probe" in
  let before = List.sort Stdlib.compare (Gamma.to_list gamma) in
  boolean "known Boolean result is disjoint from None"
    gamma false (Expr.UnOp (Not, probe));
  check "compound None type probe leaves caller gamma unchanged" true
    (before = List.sort Stdlib.compare (Gamma.to_list gamma))

let tests =
  [ "exact concrete bounds", `Quick, concrete_bounds;
    "large symbolic indices and prefixes", `Quick, abstract_large_index;
    "slice offset overflow rejection", `Quick, slice_offsets;
    "typed and wrapped SMT index aliases", `Quick, indexed_alias;
    "mathematical operator domains", `Quick, operator_domains;
    "negative and noninteger rejection", `Quick, negative_and_noninteger;
    "exact value-identity descriptor projection", `Quick, value_identity_projection;
    "value-identity binary64 component payloads", `Quick, value_identity_number_bits;
    "value-identity cycle unknown and bounds guards", `Quick, value_identity_fallbacks;
    "none equality after descriptor projection", `Quick, none_projection_equality ]
