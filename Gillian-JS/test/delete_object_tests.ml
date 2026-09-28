open Gillian.Gil_syntax
open Javert_utils.JSILNames
module Config = Gillian.Utils.Config
module Memory = Semantics.Symbolic
module Legacy = Semantics.Legacy_symbolic
module Heap = Semantics.SHeap
module PC = Engine.Gpc
module Branch = Engine.Gbranch

let key s = Expr.Lit (Literal.String s)
let name = "#loc_delete_object"
let loc = Expr.ALoc name

let pc () =
  PC.make ~matching:true
    ~pfs:(Gillian.Symbolic.Pure_context.init ())
    ~gamma:(Gillian.Symbolic.Type_env.init ())
    ()

let check msg b = Alcotest.(check bool) msg true b
let snapshot h = Yojson.Safe.to_string (Heap.to_yojson h)

let action h a args =
  let c = pc () in
  match Legacy.execute_action a h c.pfs c.gamma args with
  | Ok [ (h, _, _, _) ] -> h
  | _ -> Alcotest.fail ("setup failed: " ^ a)

let make () =
  let h = Heap.init () in
  Heap.init_object h name (Some (Expr.Lit Literal.Null));
  let h = action h (Legacy.ga_to_setter aCell) [ loc; key "z"; Expr.num 1. ] in
  let h = action h (Legacy.ga_to_setter aCell) [ loc; key "a"; Expr.num 2. ] in
  action h setProps [ loc; Expr.ESet [ key "z"; key "a" ] ]

let with_total total f =
  let saved = !Config.Verification.total in
  Fun.protect
    ~finally:(fun () -> Config.Verification.total := saved)
    (fun () ->
      Config.Verification.total := total;
      f ())

let deletes total () =
  with_total total (fun () ->
      let h = make () in
      let unrelated = "#loc_framed" in
      Heap.init_object h unrelated (Some (Expr.Lit Literal.Null));
      let before = Heap.get h unrelated in
      match Memory.execute_action delObj h (pc ()) [ loc ] with
      | [ { Branch.value = Ok (h, []); _ } ] ->
          check "target actually removed" (not (Heap.has_loc h name));
          check "unrelated object framed" (Heap.get h unrelated = before)
      | _ -> Alcotest.fail "complete unordered object was not deleted")

let rejects total mutate () =
  with_total total (fun () ->
      let h = mutate (make ()) in
      let before = snapshot h in
      let rejected =
        try
          match Memory.execute_action delObj h (pc ()) [ loc ] with
          | [ { Branch.value = Error _; _ } ] -> true
          | _ -> false
        with Gillian.Utils.Gillian_result.Exc.Gillian_error _ -> true
      in
      check "incomplete deletion rejects" rejected;
      check "rejection preserved heap" (snapshot h = before))

let missing_cell h = action h delCell [ loc; key "a" ]
let missing_domain h = action h delProps [ loc; Expr.ESet [] ]

let missing_metadata h =
  let (fs, dom), _ = Option.get (Heap.get h name) in
  Heap.set h name fs dom None;
  h

let unknown_loc h =
  Heap.remove h name;
  h

let enum_guard () =
  let h = make () in
  let c = pc () in
  let rejected =
    try
      ignore (Legacy.execute_action getAllProps h c.pfs c.gamma [ loc ]);
      false
    with
    | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
      msg
      = "Unsupported property enumeration: insertion order is unavailable \
         after logical cell production."
  in
  check "unknown enumeration still guarded" rejected

let () =
  Alcotest.run "Complete object deletion"
    [
      ( "delete",
        [
          Alcotest.test_case "total complete unknown order" `Quick
            (deletes true);
          Alcotest.test_case "partial complete unknown order" `Quick
            (deletes false);
          Alcotest.test_case "total missing cell" `Quick
            (rejects true missing_cell);
          Alcotest.test_case "partial missing cell" `Quick
            (rejects false missing_cell);
          Alcotest.test_case "total missing domain" `Quick
            (rejects true missing_domain);
          Alcotest.test_case "partial missing domain" `Quick
            (rejects false missing_domain);
          Alcotest.test_case "total missing metadata" `Quick
            (rejects true missing_metadata);
          Alcotest.test_case "partial missing metadata" `Quick
            (rejects false missing_metadata);
          Alcotest.test_case "total unknown location" `Quick
            (rejects true unknown_loc);
          Alcotest.test_case "partial unknown location" `Quick
            (rejects false unknown_loc);
          Alcotest.test_case "enumeration unchanged" `Quick enum_guard;
        ] );
    ]
