open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Reduction = Gillian.Logic.Reduction
module Config = Gillian.Utils.Config

let cat xs = Expr.NOp (LstCat, xs)
let empty = Expr.EList []
let one x = Expr.EList [ x ]
let eq a b = Expr.BinOp (a, Equal, b)
let nth xs n = Expr.BinOp (xs, LstNth, Expr.int n)
let xs = Expr.LVar "#normalization_xs"
let ys = Expr.LVar "#normalization_ys"
let zs = Expr.LVar "#normalization_zs"

let gamma () =
  let gamma = Gamma.init () in
  List.iter (fun x -> Gamma.update gamma x ListType)
    [ "#normalization_xs"; "#normalization_ys"; "#normalization_zs" ];
  gamma

let check_expr label expected actual =
  Alcotest.(check bool) label true (Expr.equal expected actual)

let reduce e = Reduction.reduce_lexpr ~gamma:(gamma ()) e

let with_total f () =
  let saved = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := saved) f

let closed_fragments () =
  let bits = [ 0L; Int64.min_int; 0x7ff8000000000042L ] in
  let numbers = List.map (fun bits -> Literal.Num (Int64.float_of_bits bits)) bits in
  let utf16 = Literal.Utf16String
      (Gillian.Utils.Utf16.of_canonical
         (Gillian.Utils.Utf16.of_code_units [ 0xd800; 0; 0xdc00 ])) in
  let source = cat [ empty; Expr.Lit (LList numbers);
    cat [ one (Expr.Lit utf16); empty; Expr.Lit (LList [ Null; Null ]) ];
    Expr.Lit (LList [ LList [ Bool true ] ]); cat [] ] in
  let expected = Expr.EList
      (List.map (fun literal -> Expr.Lit literal) (numbers @ [ utf16; Null; Null ])
       @ [ one Expr.true_ ]) in
  let actual = reduce source in
  check_expr "closed values, duplicates and nested lists retain exact shape" expected actual;
  match actual with
  | Expr.EList (Expr.Lit (Num a) :: Expr.Lit (Num b) :: Expr.Lit (Num c) :: _) ->
      Alcotest.(check (list int64)) "binary64 payloads are not canonicalized"
        bits (List.map Int64.bits_of_float [ a; b; c ])
  | _ -> Alcotest.fail "normalized literal payloads were lost"

let empty_and_open_fragments () =
  List.iter (fun source -> check_expr "all empty cats become an explicit empty list"
    empty (reduce source))
    [ cat []; cat [ empty ]; cat [ cat []; Expr.Lit (LList []); cat [ empty ] ] ];
  check_expr "singleton opaque list is retained" xs
    (reduce (cat [ empty; cat [ xs ]; empty ]));
  check_expr "literal runs coalesce without crossing symbolic segments"
    (cat [ Expr.EList [ Expr.int 1; Expr.int 2 ]; xs;
           Expr.EList [ Expr.int 3; Expr.int 4 ]; ys; one (Expr.int 5) ])
    (reduce (cat [ one (Expr.int 1); cat [ empty; one (Expr.int 2); xs ];
       Expr.Lit (LList [ Int (Z.of_int 3) ]);
       cat [ one (Expr.int 4); empty; ys ]; one (Expr.int 5) ]))

(* Bounded different bracketings have a fixed independently written flat result;
   no copy of the production normalizer is used as an oracle. *)
let rec bracketings = function
  | [] -> [ cat [] ]
  | [ x ] -> [ x ]
  | parts ->
      List.init (List.length parts - 1) (fun split ->
        let left = List.filteri (fun i _ -> i <= split) parts in
        let right = List.filteri (fun i _ -> i > split) parts in
        List.concat_map (fun left ->
          List.map (fun right -> cat [ left; right ]) (bracketings right))
          (bracketings left))
      |> List.concat

let bounded_bracketings () =
  List.iter (fun (parts, expected) ->
    List.iter (fun tree ->
      List.iter (fun source -> check_expr "parenthesization and empty wrappers"
        expected (reduce source))
        [ tree; cat [ empty; cat [ tree ]; Expr.Lit (LList []) ] ])
      (bracketings parts))
    [ ([ one (Expr.int 1); one (Expr.int 2); one (Expr.int 3);
         one (Expr.int 4); one (Expr.int 5) ],
       Expr.EList (List.init 5 (fun i -> Expr.int (i + 1))));
      ([ one (Expr.int 1); xs; one (Expr.int 2); ys; one (Expr.int 3) ],
       cat [ one (Expr.int 1); xs; one (Expr.int 2); ys; one (Expr.int 3) ]) ]

let large_cat_shapes () =
  let values = List.init 2048 Expr.int in
  let left = List.fold_left (fun acc value -> cat [ acc; one value ]) empty values in
  let right = List.fold_left (fun acc value -> cat [ one value; acc ]) empty
      (List.rev values) in
  List.iter (fun source -> check_expr "large skew retains every element in order"
    (Expr.EList values) (reduce source)) [ left; right ];
  check_expr "flat literal runs retain order" (Expr.EList values)
    (reduce (cat (List.map one values)));
  let alternating = List.concat_map (fun i -> [ one (Expr.int i); xs ])
      (List.init 512 Fun.id) in
  check_expr "large alternating segments are neither dropped nor reordered"
    (cat alternating) (reduce (cat alternating))

let contextual_nested_cats () =
  let gamma = gamma () in
  let pfs = Engine.PFS.of_list [ eq xs empty ] in
  let before = Engine.PFS.to_list pfs in
  let gamma_before = Hashtbl.fold (fun name typ acc -> (name, typ) :: acc)
      (Gamma.as_hashtbl gamma) [] |> List.sort Stdlib.compare in
  let source = cat [ zs; cat [ xs; ys ]; one (Expr.int 9) ] in
  check_expr "nested Cat still receives the contextual empty-prefix rewrite"
    (cat [ zs; ys; one (Expr.int 9) ])
    (Reduction.reduce_lexpr ~gamma ~pfs source);
  check_expr "the same syntax without that PFS still retains xs"
    (cat [ zs; xs; ys; one (Expr.int 9) ]) (reduce source);
  let slice start count = Expr.LstSub (xs, Expr.int start, Expr.int count) in
  check_expr "slice fusion inside a Cat is not skipped behind an opaque prefix"
    (cat [ zs; slice 0 5; ys ])
    (reduce (cat [ zs; cat [ slice 0 2; slice 2 3 ]; ys ]));
  Alcotest.(check bool) "caller facts remain exact" true
    (List.equal Expr.equal before (Engine.PFS.to_list pfs));
  let gamma_after = Hashtbl.fold (fun name typ acc -> (name, typ) :: acc)
      (Gamma.as_hashtbl gamma) [] |> List.sort Stdlib.compare in
  Alcotest.(check bool) "caller types remain exact" true (gamma_before = gamma_after)

let failure e =
  match reduce e with
  | _ -> Alcotest.fail "a required malformed list expression was accepted"
  | exception Reduction.ReductionException (expression, message) -> expression, message

let check_failure label (expected, message) source =
  let actual, actual_message = failure source in
  check_expr (label ^ " expression") expected actual;
  Alcotest.(check string) (label ^ " message") message actual_message

let required_error_order () =
  let bad_nth = nth empty 0 and bad_head = Expr.UnOp (Car, empty) in
  let nth_failure = failure bad_nth and head_failure = failure bad_head in
  Alcotest.(check bool) "the competing failures are distinguishable" false
    (Expr.equal (fst nth_failure) (fst head_failure));
  check_failure "left required leaf fails first" nth_failure
    (cat [ cat [ one bad_nth ]; cat [ one bad_head ] ]);
  check_failure "reversing required leaves reverses first failure" head_failure
    (cat [ cat [ one bad_head ]; cat [ one bad_nth ] ])

let boolean_required_and_skipped () =
  let bad = nth empty 0 in
  let bad_bool = eq bad (Expr.Lit Null) in
  List.iter (fun (op, skipped, expected, required) ->
    check_expr "skipped Boolean operand is not evaluated inside a Cat leaf"
      (cat [ one (Expr.bool expected); xs ])
      (reduce (cat [ one (Expr.BinOp (Expr.bool skipped, op, bad_bool)); xs ]));
    ignore (failure (cat [ one (Expr.BinOp (Expr.bool required, op, bad_bool)); xs ])))
    [ And, false, false, true; Or, true, true, false; Impl, false, true, true ];
  check_failure "false RHS cannot erase a required failing LHS" (failure bad)
    (cat [ one (Expr.BinOp (bad_bool, And, Expr.false_)); xs ])

exception Missing_domain

let partial_domains () =
  let proves expression = Expr.equal (reduce expression) Expr.true_ in
  let domain expression =
    Engine.Totality.check_expression ~proof:true
      ~require:(fun _ condition -> if not (proves condition) then raise Missing_domain)
      ~proves ~evaluate:Fun.id expression
  in
  domain (cat [ empty; one (Expr.Lit Null); cat [] ]);
  List.iter (fun source ->
    let rejected = match domain source with
      | () -> false
      | exception Missing_domain -> true
      | exception Reduction.ReductionException _ -> true in
    Alcotest.(check bool) "normalization cannot grant missing list domains" true rejected)
    [ Expr.UnOp (Car, cat [ empty; cat [] ]);
      cat [ empty; Expr.Lit Null; empty ];
      cat [ empty; Expr.LstSub (empty, Expr.int (-1), Expr.int 1) ] ]

let quantified_scope () =
  let gamma = gamma () in
  let pfs = Engine.PFS.of_list [ eq xs empty ] in
  let source = Expr.ForAll ([ "#normalization_xs", Some ListType ],
      eq (cat [ xs; one Expr.true_ ]) (one Expr.true_)) in
  let result = Reduction.reduce_lexpr ~gamma ~pfs source in
  Alcotest.(check bool) "outer facts do not turn a bound Cat variable into empty" true
    (match result with Expr.ForAll _ -> true | _ -> false);
  Alcotest.(check bool) "bound-variable processing preserves caller facts" true
    (List.equal Expr.equal [ eq xs empty ] (Engine.PFS.to_list pfs));
  Alcotest.(check bool) "bound-variable processing preserves caller type" true
    (Gamma.get gamma "#normalization_xs" = Some ListType)

let tests = List.map (fun (name, f) -> Alcotest.test_case name `Quick (with_total f))
  [ "closed literal identity", closed_fragments;
    "empty and open fragments", empty_and_open_fragments;
    "bounded Cat bracketings", bounded_bracketings;
    "large Cat shapes", large_cat_shapes;
    "contextual nested Cat rewrites", contextual_nested_cats;
    "required first-error order", required_error_order;
    "Boolean required and skipped operands", boolean_required_and_skipped;
    "original partial domains", partial_domains;
    "quantified Cat scope", quantified_scope ]
