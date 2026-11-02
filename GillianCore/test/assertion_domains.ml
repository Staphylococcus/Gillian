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

let check ?(unknown = false) ?(unknown_before_type = false)
    ?(observe_assertion = fun _ _ -> ())
    ?(observe_assume = fun _ _ _ -> ()) bindings facts obligations =
  let gamma = Gamma.init () in
  List.iter (fun (n, t) -> Gamma.update gamma n t) bindings;
  let calls = ref 0 in
  let evaluate facts e =
    Reduction.reduce_lexpr ~gamma ~pfs:(Engine.PFS.of_list facts) e
  in
  let assertion facts e =
    observe_assertion facts e;
    if unknown_before_type && Expr.equal e (typ index Type.NumberType)
       && not (List.exists (Expr.equal (typ index Type.NumberType)) facts) then
      raise Required_unknown;
    Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
      [e] gamma
  in
  let assume facts ready =
    incr calls;
    if unknown then raise Required_unknown;
    let next =
      if Solver.check_satisfiability (ready @ facts) gamma then
        Some (ready @ facts)
      else None
    in
    observe_assume facts ready next;
    next
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

let type_before_dependent_fact () =
  let calls = check ~unknown_before_type:true [] []
    [fact (Expr.UnOp (IsInt, index)); fact (typ index Type.NumberType);
     value (Expr.UnOp (NumberToUtf16, index))] in
  Alcotest.(check int) "type fact precedes dependent domain queries" 1 calls

let tests = List.map (fun (name, f) -> Alcotest.test_case name `Quick (with_total f))
  ["existing value domain", already_defined; "new type fact", needs_fact;
   "missing domain", missing_domain; "no self justification", no_self_justification;
   "required unknown", required_unknown;
   "type before dependent fact", type_before_dependent_fact]

(* These exercise the real metadata preparation, not execution or rank descent.
   Conditions remain symbolic: both ordinary and exceptional edges must count. *)
let cfg_invariant =
  Cmd.Logic (LCmd.SL (SLCmd.Invariant ([], [], Some (Expr.int 0))))

let cfg_proc name commands : (Annot.Basic.t, int) Proc.t =
  { proc_name = name; proc_source_path = None; proc_internal = false;
    proc_body = Array.mapi
      (fun i cmd -> (Annot.Basic.make_basic (), Some i, cmd)) commands;
    proc_params = []; proc_spec = None; proc_aliases = []; proc_calls = [];
    proc_display_name = None; proc_hidden = false }

let cfg_prepare proc =
  let predecessors = Hashtbl.create 16 in
  let incoming = Hashtbl.create 16 in
  Array.iteri (fun i (_, _, cmd) ->
    List.iter (fun j ->
      let selected = Option.value ~default:0 (Hashtbl.find_opt incoming j) in
      Hashtbl.add predecessors (proc.Proc.proc_name, i, j) selected;
      Hashtbl.replace incoming j (selected + 1)) (Cmd.successors cmd i))
    proc.proc_body;
  let snapshot = Array.copy proc.proc_body in
  let predecessor_snapshot = Hashtbl.copy predecessors in
  let unchanged () =
    Alcotest.(check bool) "input body, PHIs and annotations unchanged" true
      (snapshot = proc.proc_body);
    Alcotest.(check int) "predecessor count unchanged"
      (Hashtbl.length predecessor_snapshot) (Hashtbl.length predecessors);
    Hashtbl.iter (fun key value ->
      Alcotest.(check (option int)) "incoming predecessor index unchanged"
        (Some value) (Hashtbl.find_opt predecessors key)) predecessor_snapshot
  in
  Fun.protect ~finally:unchanged (fun () ->
    Totality.prepare_loops ~set_loop_info:Annot.Basic.set_loop_info
      ~macros:(Hashtbl.create 0) ~predecessors proc)

let cfg_accept name commands expected =
  let proc = cfg_proc name commands in
  let prepared = cfg_prepare proc in
  Alcotest.(check int) "body length preserved" (Array.length commands)
    (Array.length prepared.proc_body);
  Array.iteri (fun i (annot, label, cmd) ->
    let _, original_label, original_cmd = proc.proc_body.(i) in
    Alcotest.(check bool) "original command/PHI and label preserved" true
      (label = original_label && cmd = original_cmd);
    Alcotest.(check (list string)) ("loop metadata at " ^ string_of_int i)
      (expected i) (Annot.Basic.get_loop_info annot)) prepared.proc_body

let cfg_reject name reason commands =
  match cfg_prepare (cfg_proc name commands) with
  | _ -> Alcotest.fail "reachable unsupported loop was accepted"
  | exception Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
      Alcotest.(check string) "exact totality rejection"
        ("Unsupported totality proof: " ^ name ^ reason) msg

let cfg_post_throw () =
  let empty = Expr.Lit Literal.Empty in
  [| Cmd.Goto 4; Cmd.Goto 12;
     Cmd.Assignment ("dead_completion", empty); Cmd.Goto 8;
     Cmd.PhiAssignment ["completion", [empty; empty]]; cfg_invariant;
     Cmd.GuardedGoto (Expr.PVar "loop", 7, 11);
     Cmd.GuardedGoto (Expr.PVar "throw_now", 1, 8);
     Cmd.PhiAssignment ["merge_completion", [empty; empty]];
     Cmd.Skip; Cmd.Goto 4; Cmd.ReturnNormal; Cmd.ReturnError |]

let cfg_reachable_metadata () =
  let name = "post_throw" in
  cfg_accept name (cfg_post_throw ())
    (fun i -> if i >= 4 && i <= 10 then [name ^ "#ranked-loop-5"] else []);
  (* Dead cycles must neither acquire loop metadata nor reject a reachable
     acyclic procedure. The ranked case also checks the final invariant gate. *)
  cfg_accept "dead_unranked" [|Cmd.Goto 1; Cmd.ReturnNormal; Cmd.Goto 2|]
    (fun _ -> []);
  cfg_accept "dead_ranked"
    [|Cmd.Goto 1; Cmd.ReturnNormal; cfg_invariant; Cmd.Goto 2|]
    (fun _ -> []);
  cfg_accept "entry_zero"
    [|cfg_invariant; Cmd.GuardedGoto (Expr.PVar "loop", 2, 3);
      Cmd.Goto 0; Cmd.ReturnNormal|]
    (fun i -> if i < 3 then ["entry_zero#ranked-loop-0"] else [])

let cfg_reachable_guards () =
  let bypass = " has an entry bypassing its ranked header." in
  let conditional = cfg_post_throw () in
  conditional.(0) <- Cmd.GuardedGoto (Expr.PVar "bypass", 3, 4);
  cfg_reject "conditional_bypass" bypass conditional;
  let exceptional = cfg_post_throw () in
  exceptional.(0) <- Cmd.call ~error:3 "result" (Expr.string "may_throw") [];
  exceptional.(1) <- Cmd.Goto 4;
  exceptional.(7) <- Cmd.GuardedGoto (Expr.PVar "throw_now", 12, 8);
  cfg_reject "exceptional_bypass" bypass exceptional;
  let missing = cfg_post_throw () in
  missing.(5) <- Cmd.Skip;
  cfg_reject "missing_rank"
    " has a control-flow cycle without a ranked invariant header." missing;
  cfg_reject "reachable_unmatched"
    " contains an operation outside the totality fragment: invariant."
    [|cfg_invariant; Cmd.ReturnNormal|]

let cfg_nested_metadata () =
  let commands =
    [|cfg_invariant; Cmd.GuardedGoto (Expr.PVar "outer", 2, 9);
      Cmd.Goto 3; cfg_invariant;
      Cmd.GuardedGoto (Expr.PVar "inner", 5, 7); Cmd.Skip; Cmd.Goto 3;
      Cmd.Skip; Cmd.Goto 0; Cmd.ReturnNormal|] in
  cfg_accept "nested" commands (fun i ->
    if i = 9 then []
    else if i >= 3 && i <= 6 then
      ["nested#ranked-loop-3"; "nested#ranked-loop-0"]
    else ["nested#ranked-loop-0"]);
  (* Node 2 is outside the child SCC but globally reachable through its parent.
     Its second symbolic edge must still prevent an entry below the header. *)
  commands.(2) <- Cmd.GuardedGoto (Expr.PVar "inner_bypass", 3, 5);
  cfg_reject "nested_bypass" " has an entry bypassing its ranked header."
    commands

let tests = tests @ List.map (fun (name, f) ->
  Alcotest.test_case name `Quick (with_total f))
  ["reachable loop metadata post-throw PHIs and dead cycles", cfg_reachable_metadata;
   "reachable loop guards retain conditional and exception edges", cfg_reachable_guards;
   "nested loop metadata retains globally reachable parent entries", cfg_nested_metadata]

(* The observer injects only a required-query failure, never a truth value.
   All other domain checks and every consistency check use the real solver. *)
let mentions_domain_list expression =
  let found = ref false in
  ignore (Expr.map_opt (fun e ->
    if Expr.equal e xs then found := true;
    (Some e, true)) None expression);
  !found

let staged_number_fixture () =
  let current = Expr.LVar "#domain_current" in
  let predecessor = Expr.BinOp
    (Expr.BinOp (index, FPlus, Expr.num 1.), FMinus, Expr.num 1.) in
  let cast e = Expr.UnOp (NumToInt, e) in
  let length = Expr.UnOp (LstLen, xs) in
  let bound = Expr.BinOp (cast index, ILessThan, length) in
  let lookup = Expr.BinOp (xs, LstNth, cast predecessor) in
  let lookup_fact = Expr.BinOp (current, ValueEqual, lookup) in
  let bindings = ["#domain_index", Type.NumberType;
    "#domain_xs", Type.ListType; "#domain_current", Type.Utf16Type] in
  let facts = [Expr.UnOp (IsInt, index);
    Expr.BinOp (Expr.num 0., FLessThanEqual, index);
    Expr.BinOp (index, FLessThanEqual, Expr.num 100.);
    Expr.BinOp (predecessor, Equal, index)] in
  let gamma = Gamma.init () in
  List.iter (fun (name, typ) -> Gamma.update gamma name typ) bindings;
  let reduce = Reduction.reduce_lexpr ~gamma ~pfs:(Engine.PFS.of_list facts) in
  let finite_query = reduce (Expr.BinOp
    (Expr.num (-.Float.max_float), FLessThanEqual, index)) in
  (* This is a genuinely solver-assisted round, not an already-quick type test.
     The old fold reaches the dependent domain before staging the checked bound,
     even if the independent bound occurs first in the input. *)
  Alcotest.(check bool) "cast domain is not a quick literal" false
    (Expr.equal finite_query Expr.true_ || Expr.equal finite_query Expr.false_);
  Alcotest.(check bool) "cast domain does not mention the list" false
    (mentions_domain_list finite_query);
  Alcotest.(check bool) "lookup still has a pending list-domain request" true
    (mentions_domain_list (reduce
      (Expr.BinOp (cast predecessor, ILessThan, length))));
  (bindings, facts, bound, lookup, lookup_fact, finite_query)

let staged_number_bound () =
  let bindings, facts, bound, lookup, lookup_fact, _ = staged_number_fixture () in
  List.iter (fun (label, pending) ->
    let premature = ref false in
    let staged = ref 0 in
    let bound_staged = ref 0 in
    let lookup_staged = ref 0 in
    let lookup_pending = List.exists (fun obligation ->
      match Asrt.as_definedness obligation with
      | Some (true, e) -> Expr.equal e lookup_fact
      | _ -> false) pending in
    let observe_assertion scratch condition =
      if mentions_domain_list condition
         && not (List.exists (Expr.equal bound) scratch) then (
        premature := true;
        raise Required_unknown)
    in
    let observe_assume scratch ready next =
      Alcotest.(check bool) (label ^ " each checked stage has a real consistent state") true
        (Option.is_some next);
      if List.equal Expr.equal ready [bound] then (
        Alcotest.(check int) (label ^ " the bound is the first stage") 0 !staged;
        Alcotest.(check int) (label ^ " the bound is not restaged") 0 !bound_staged;
        incr bound_staged)
      else (
        Alcotest.(check bool) (label ^ " a lookup fact is actually pending") true lookup_pending;
        Alcotest.(check bool) (label ^ " only that checked lookup may follow") true
          (List.equal Expr.equal ready [lookup_fact]);
        Alcotest.(check int) (label ^ " the bound was already staged") 1 !bound_staged;
        Alcotest.(check bool) (label ^ " old scratch already contains the bound") true
          (List.exists (Expr.equal bound) scratch);
        Alcotest.(check int) (label ^ " the lookup is not restaged") 0 !lookup_staged;
        incr lookup_staged);
      incr staged
    in
    let calls = check ~observe_assertion ~observe_assume bindings facts
      pending in
    Alcotest.(check bool) (label ^ " no premature list-domain request") false !premature;
    Alcotest.(check int) (label ^ " exact bound staging was observed once") 1 !bound_staged;
    Alcotest.(check int) (label ^ " calls equal observed real stages") !staged calls;
    if not lookup_pending then
      Alcotest.(check int) (label ^ " value-only case stages only the bound") 1 calls)
    ["lookup first", [fact lookup_fact; fact bound; value lookup];
     "bound first", [fact bound; fact lookup_fact; value lookup];
     "value only, bound first", [fact bound; value lookup];
     "value only, value first", [value lookup; fact bound]]

let staged_missing_bound () =
  let bindings, facts, _, lookup, _, _ = staged_number_fixture () in
  let pending = [fact (Expr.UnOp (IsInt, index)); value lookup] in
  List.iter (fun obligations ->
    expect_domain_rejection "missing symbolic list bound stays rejected" (fun () ->
      check bindings facts obligations)) [pending; List.rev pending]

let staged_no_self_justification () =
  let bindings, facts, _, lookup, lookup_fact, _ = staged_number_fixture () in
  let pending = [fact lookup_fact; value lookup] in
  List.iter (fun obligations ->
    expect_domain_rejection "pending lookup fact cannot provide its own bound" (fun () ->
      check bindings facts obligations)) [pending; List.rev pending]

let staged_required_unknown () =
  let bindings, facts, bound, lookup, lookup_fact, finite_query = staged_number_fixture () in
  List.iter (fun pending ->
    let reached = ref false in
    let observe_assertion _ condition =
      if Expr.equal condition finite_query then (reached := true; raise Required_unknown)
    in
    Alcotest.check_raises "required cast-domain unknown still escapes"
      Required_unknown (fun () -> ignore (check ~observe_assertion bindings facts
        (pending @ [value lookup])));
    Alcotest.(check bool) "required cast-domain query was reached" true !reached)
    [[fact lookup_fact; fact bound]; [fact bound; fact lookup_fact]]

let staged_infeasible_bound () =
  let bindings, facts, bound, lookup, lookup_fact, _ = staged_number_fixture () in
  let facts = Expr.BinOp (Expr.UnOp (LstLen, xs), ILessThanEqual, Expr.int 0) :: facts in
  List.iter (fun pending ->
    let observe_assume _ ready next =
      Alcotest.(check bool) "only the independently checked bound is assumed" true
        (List.equal Expr.equal ready [bound]);
      Alcotest.(check bool) "real solver rejects the contradictory scratch state" true
        (Option.is_none next)
    in
    let calls = check ~observe_assume bindings facts (pending @ [value lookup]) in
    Alcotest.(check int) "checked contradictory bound is genuine infeasibility" 1 calls)
    [[fact lookup_fact; fact bound]; [fact bound; fact lookup_fact]]

let tests = tests @ List.map (fun (name, f) ->
  Alcotest.test_case name `Quick (with_total f))
  ["symbolic Number bound precedes nested predecessor lookup in both orders", staged_number_bound;
   "symbolic Number lookup without its list bound is rejected", staged_missing_bound;
   "symbolic Number lookup cannot justify its pending domain", staged_no_self_justification;
   "required staged Number cast unknown propagates in both orders", staged_required_unknown;
   "staged contradictory Number bound retains genuine infeasibility", staged_infeasible_bound]
