open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Reduction = Gillian.Logic.Reduction
module Totality = Engine.Totality
module Config = Gillian.Utils.Config

exception Required_unknown

let with_total f () =
  let saved = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := saved) f

let index = Expr.LVar "#domain_index"
let xs = Expr.LVar "#domain_xs"
let unrelated = Expr.LVar "#domain_unrelated"
let fact e = Asrt.definedness ~fact:true e
let value e = Asrt.definedness ~fact:false e
let typ e t = Expr.BinOp (Expr.UnOp (TypeOf, e), Equal, Expr.Lit (Type t))
let at = Expr.BinOp (xs, LstNth, Expr.int 0)

let check ?(unknown = false) bindings facts obligations =
  let gamma = Gamma.init () in
  List.iter (fun (n, t) -> Gamma.update gamma n t) bindings;
  let calls = ref 0 in
  let evaluate facts e =
    Reduction.reduce_lexpr ~gamma ~pfs:(Engine.PFS.of_list facts) e
  in
  let assertion facts e =
    Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
      [e] gamma
  in
  let assume facts ready =
    incr calls;
    if unknown then raise Required_unknown;
    if Solver.check_satisfiability (ready @ facts) gamma then
      Some (ready @ facts)
    else None
  in
  Totality.check_assertion_production ~evaluate ~assertion ~assume facts obligations;
  !calls

let already_defined () =
  let calls = check ~unknown:true
    ["#domain_index", Type.NumberType; "#domain_unrelated", Type.BooleanType]
    [] [fact unrelated; value (Expr.UnOp (NumberToUtf16, index))] in
  Alcotest.(check int) "already defined conversion needs no consistency query" 0 calls

let needs_fact () =
  let calls = check [] []
    [fact (typ index Type.NumberType); value (Expr.UnOp (NumberToUtf16, index))] in
  Alcotest.(check int) "new checked type fact is still established" 1 calls

let expect_domain_rejection label run =
  match run () with
  | _ -> Alcotest.fail "undefined expression was accepted"
  | exception Gillian.Utils.Gillian_result.Exc.Gillian_error (AnalysisFailures [{msg; _}]) ->
      Alcotest.(check bool) label true
        (String.starts_with ~prefix:"Produced assertion is not proved defined:" msg)

let missing_domain () =
  expect_domain_rejection "missing Number domain is rejected" (fun () ->
    check [] [] [value (Expr.UnOp (NumberToUtf16, index))])

let no_self_justification () =
  expect_domain_rejection "unchecked indexing cannot justify its own domain" (fun () ->
    check ["#domain_xs", Type.ListType] []
      [fact (Expr.BinOp (at, Equal, Expr.int 7)); value at])

let required_unknown () =
  Alcotest.check_raises "required consistency unknown still escapes"
    Required_unknown (fun () -> ignore (check ~unknown:true [] []
      [fact (typ index Type.NumberType); value (Expr.UnOp (NumberToUtf16, index))]))

let tests = List.map (fun (name, f) -> Alcotest.test_case name `Quick (with_total f))
  ["existing value domain", already_defined; "new type fact", needs_fact;
   "missing domain", missing_domain; "no self justification", no_self_justification;
   "required unknown", required_unknown]
