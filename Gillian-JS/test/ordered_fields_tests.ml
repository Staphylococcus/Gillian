open Gillian.Gil_syntax
open Javert_utils.JSILNames
module Memory = Semantics.Symbolic
module Legacy = Semantics.Legacy_symbolic
module Heap = Semantics.SHeap
module Fields = Semantics.SFVL
module PC = Engine.Gpc
module Branch = Engine.Gbranch

let key s = Expr.Lit (Literal.String s)
let keys xs = Expr.EList (List.map key xs)
let values = Expr.EList [ Expr.num 1.; Expr.num 2. ]
let loc_name = "#loc_ordered_resource"
let loc = Expr.ALoc loc_name
let metadata = Expr.ALoc "#loc_ordered_metadata"

let pc () =
  PC.make ~matching:true
    ~pfs:(Gillian.Symbolic.Pure_context.init ())
    ~gamma:(Gillian.Symbolic.Type_env.init ())
    ()

let check msg condition = Alcotest.(check bool) msg true condition
let snapshot h = Yojson.Safe.to_string (Heap.to_yojson h)

let action ?(context = pc ()) h name args =
  match Legacy.execute_action name h context.pfs context.gamma args with
  | Ok [ (heap, out, _, _) ] -> (heap, out)
  | _ -> Alcotest.fail ("action failed: " ^ name)

let make () =
  let heap = Heap.init () in
  Heap.init_object heap loc_name (Some metadata);
  let heap, _ = action heap setCell [ loc; key "z"; Expr.num 1. ] in
  let heap, _ = action heap setCell [ loc; key "a"; Expr.num 2. ] in
  let heap, _ = action heap setProps [ loc; Expr.ESet [ key "z"; key "a" ] ] in
  heap

let consume ?(context = pc ()) heap =
  match Memory.consume aOrderedFields heap context [ loc ] with
  | [ { Branch.value = Ok (heap, out); _ } ] -> (heap, out)
  | _ -> Alcotest.fail "real consume failed"

let produce ?(context = pc ()) heap ks vs =
  match Memory.produce aOrderedFields heap context [ loc; ks; vs ] with
  | [ { Branch.value = heap; _ } ] -> heap
  | _ -> Alcotest.fail "real produce failed"

let has_order heap order =
  snd (action heap getAllProps [ loc ]) = [ loc; keys order ]

let reject_consume heap =
  let before = snapshot heap in
  let rejected =
    match Memory.consume aOrderedFields heap (pc ()) [ loc ] with
    | [ { Branch.value = Error _; _ } ] -> true
    | _ -> false
  in
  check "consumer rejected missing ownership" rejected;
  check "rejected consume left original heap intact" (before = snapshot heap)

let reject_produce heap ks vs =
  let before = snapshot heap in
  check "producer rejected invalid/overlapping resource"
    (Memory.produce aOrderedFields heap (pc ()) [ loc; ks; vs ] = []);
  check "rejected producer left original heap intact" (before = snapshot heap)

let roundtrip () =
  let original = make () in
  let before = snapshot original in
  let remainder, outs = consume original in
  check "real outputs include order and values"
    (outs = [ keys [ "z"; "a" ]; values ]);
  check "consumer did not mutate input branch" (before = snapshot original);
  (match Heap.get remainder loc_name with
  | Some ((fields, None), Some md) ->
      check "exclusive consume removed fields" (Fields.is_empty fields);
      check "metadata framed" (md = metadata)
  | _ ->
      Alcotest.fail "consume did not remove exactly the field/domain footprint");
  let restored = produce remainder (List.hd outs) (List.nth outs 1) in
  check "actual enumeration restored" (has_order restored [ "z"; "a" ]);
  check "actual z value restored"
    (snd (action restored getCell [ loc; key "z" ])
    = [ loc; key "z"; Expr.num 1. ]);
  check "actual a value restored"
    (snd (action restored getCell [ loc; key "a" ])
    = [ loc; key "a"; Expr.num 2. ]);
  check "metadata retained through production"
    (snd (action restored getMetadata [ loc ]) = [ loc; metadata ])

let reinsert () =
  let heap = make () in
  let heap, _ = action heap setCell [ loc; key "z"; Expr.Lit Literal.Nono ] in
  let heap, _ = action heap setCell [ loc; key "z"; Expr.num 3. ] in
  let remainder, out = consume heap in
  check "new order observes real reinsert"
    (out = [ keys [ "a"; "z" ]; Expr.EList [ Expr.num 2.; Expr.num 3. ] ]);
  check "old witness is false" (List.hd out <> keys [ "z"; "a" ]);
  let restored = produce remainder (List.hd out) (List.nth out 1) in
  check "updated order survives resource production"
    (has_order restored [ "a"; "z" ])

let incomplete () =
  let heap = make () in
  let heap, _ =
    action heap setProps [ loc; Expr.ESet [ key "z"; key "a"; key "hole" ] ]
  in
  reject_consume heap;
  let heap = make () in
  let heap, _ = action heap delCell [ loc; key "a" ] in
  reject_consume heap;
  let heap = make () in
  let heap, _ = action heap delProps [ loc; Expr.ESet [] ] in
  reject_consume heap

let exposed_absence () =
  let heap = make () in
  let heap, _ =
    action heap setProps
      [ loc; Expr.ESet [ key "z"; key "a"; key "Symbol"; key "errors" ] ]
  in
  let heap, _ =
    action heap
      (Legacy.ga_to_setter aCell)
      [ loc; key "Symbol"; Expr.Lit Literal.Nono ]
  in
  let heap, _ =
    action heap
      (Legacy.ga_to_setter aCell)
      [ loc; key "errors"; Expr.Lit Literal.Nono ]
  in
  let remainder, outs = consume heap in
  check "exposed absence excluded from present witness"
    (outs = [ keys [ "z"; "a" ]; values ]);
  let restored = produce remainder (List.hd outs) (List.nth outs 1) in
  check "full absence domain retained"
    (snd (action restored getCell [ loc; key "errors" ])
    = [ loc; key "errors"; Expr.Lit Literal.Nono ])

let overlap () =
  reject_produce (make ()) (keys [ "z"; "a" ]) values;
  let heap = Heap.init () in
  Heap.init_object heap loc_name (Some metadata);
  reject_produce heap (keys []) (keys []);
  let heap = Heap.init () in
  Heap.set heap loc_name
    (Fields.add_abstract (key "errors") (Expr.Lit Literal.Nono) Fields.empty)
    None (Some metadata);
  reject_produce heap (keys [ "z"; "a" ]) values

let malformed () =
  let heap = Heap.init () in
  let typed s =
    Expr.Lit
      (Literal.Utf16String
         (Gillian.Utils.Utf16.of_canonical (Gillian.Utils.Utf16.canonical s)))
  in
  List.iter
    (fun (ks, vs) -> reject_produce heap ks vs)
    [
      (keys [ "z"; "z" ], values);
      (Expr.EList [ key "z"; typed "z" ], values);
      (keys [ "z" ], values);
      (keys [ "z" ], Expr.EList [ Expr.Lit Literal.Nono ]);
      (keys [ "z" ], Expr.EList [ Expr.LVar "#unknown_value" ]);
      (keys [ "10"; "2" ], values);
      (Expr.EList [ Expr.LVar "#unknown_key" ], Expr.EList [ Expr.num 1. ]);
      (Expr.num 1., values);
    ];
  let restored = produce heap (keys [ "2"; "10" ]) values in
  check "canonical indices valid" (has_order restored [ "2"; "10" ])

let empty_and_metadata () =
  let heap = Heap.init () in
  Heap.set heap loc_name Fields.empty None (Some metadata);
  let restored = produce heap (Expr.Lit (Literal.LList [])) (Expr.EList []) in
  check "empty resource owns a complete empty domain" (has_order restored []);
  let remainder, outs = consume restored in
  check "empty outputs" (outs = [ keys []; keys [] ]);
  check "metadata alone survives"
    (Heap.get remainder loc_name = Some ((Fields.empty, None), Some metadata))

let unknown_and_actions () =
  let heap = make () in
  let heap, _ =
    action heap (Legacy.ga_to_setter aCell) [ loc; key "z"; Expr.num 1. ]
  in
  let before = snapshot heap in
  let rejects f =
    let rejected =
      try
        f ();
        false
      with
      | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError text) ->
        text
        = "Unsupported property enumeration: insertion order is unavailable \
           after logical cell production."
    in
    check "existing unknown-order guard" rejected
  in
  rejects (fun () ->
      ignore (Memory.consume aOrderedFields heap (pc ()) [ loc ]));
  rejects (fun () -> ignore (action heap getAllProps [ loc ]));
  check "unknown guard does not mutate heap" (before = snapshot heap);
  check "resource exclusive" (not (Memory.is_overlapping_asrt aOrderedFields));
  List.iter
    (fun (name, arity) ->
      check "logical action not total" (not (Memory.is_action_total name arity)))
    [ (getOrderedFields, 1); (setOrderedFields, 3); (delOrderedFields, 1) ]

let copying () =
  let h = produce (Heap.init ()) (keys [ "z"; "a" ]) values in
  let restored =
    match Heap.of_yojson (Heap.to_yojson h) with
    | Ok h -> h
    | Error e -> Alcotest.fail e
  in
  List.iter
    (fun h ->
      check "known resource provenance survives copy/JSON"
        (has_order h [ "z"; "a" ]))
    [ Heap.copy h; restored ]

(* Use the real memory producer, as loop frame restoration does. A value-only
   exporter cannot pass these order checks, even if its cell values survive. *)
let restore_assertions assertions =
  List.fold_left
    (fun heap -> function
      | Asrt.CorePred (name, ins, outs) -> (
          match Memory.produce name heap (pc ()) (ins @ outs) with
          | [ { Branch.value = heap; _ } ] -> heap
          | _ -> Alcotest.fail ("exported resource cannot be restored: " ^ name)
          )
      | _ -> Alcotest.fail "unexpected non-core heap assertion")
    (Heap.init ()) assertions

let exports_order assertions =
  List.exists
    (function
      | Asrt.CorePred (name, _, _) -> name = aOrderedFields
      | _ -> false)
    assertions

let frame_export () =
  let original = make () in
  ignore (action original getCell [ loc; key "absent" ]);
  let before = snapshot original in
  let assertions = Heap.assertions original in
  check "full frame exports its order" (exports_order assertions);
  check "export does not mutate frame" (before = snapshot original);
  let restored = restore_assertions assertions in
  check "frame order survives" (has_order restored [ "z"; "a" ]);
  check "frame values survive"
    (snd (action restored getCell [ loc; key "z" ])
    = [ loc; key "z"; Expr.num 1. ]);
  check "materialized absence remains absent"
    (snd (action restored getCell [ loc; key "absent" ])
    = [ loc; key "absent"; Expr.Lit Literal.Nono ]);
  check "metadata exported separately"
    (snd (action restored getMetadata [ loc ]) = [ loc; metadata ])

let frame_export_mutation () =
  let heap = restore_assertions (Heap.assertions (make ())) in
  ignore (action heap setCell [ loc; key "z"; Expr.Lit Literal.Nono ]);
  ignore (action heap setCell [ loc; key "z"; Expr.num 3. ]);
  let restored = restore_assertions (Heap.assertions heap) in
  check "export observes deletion and reinsertion"
    (has_order restored [ "a"; "z" ]);
  check "export cannot reuse stale values"
    (snd (action restored getCell [ loc; key "z" ])
    = [ loc; key "z"; Expr.num 3. ])

let conservative_export () =
  let cases =
    [
      ( "partial domain",
        fun h ->
          ignore
            (action h setProps
               [ loc; Expr.ESet [ key "z"; key "a"; key "hole" ] ]) );
      ( "missing domain",
        fun h -> ignore (action h delProps [ loc; Expr.ESet [] ]) );
      ( "unknown value presence",
        fun h ->
          ignore (action h setCell [ loc; key "a"; Expr.LVar "#unknown" ]) );
      ( "unknown insertion order",
        fun h ->
          ignore
            (action h (Legacy.ga_to_setter aCell) [ loc; key "a"; Expr.num 2. ])
      );
      ( "canonical name collision",
        fun h ->
          let alias =
            Expr.Lit
              (Literal.Utf16String
                 (Gillian.Utils.Utf16.of_canonical
                    (Gillian.Utils.Utf16.canonical "a")))
          in
          ignore (action h setCell [ loc; alias; Expr.num 3. ]);
          ignore
            (action h setProps [ loc; Expr.ESet [ key "z"; key "a"; alias ] ])
      );
    ]
  in
  List.iter
    (fun (label, alter) ->
      let heap = make () in
      alter heap;
      let before = snapshot heap in
      let assertions = Heap.assertions heap in
      check
        (label ^ " retains conservative cells")
        (not (exports_order assertions));
      check (label ^ " leaves original intact") (snapshot heap = before))
    cases;
  let heap = make () in
  ignore (action heap (Legacy.ga_to_setter aCell) [ loc; key "a"; Expr.num 2. ]);
  let restored = restore_assertions (Heap.assertions heap) in
  let rejected =
    try
      ignore (action restored getAllProps [ loc ]);
      false
    with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) ->
      true
  in
  check "export never certifies an unknown order" rejected

let symbolic_context typ =
  let context = pc () in
  Gillian.Symbolic.Type_env.update context.gamma "#symbolic_key" typ;
  context

let symbolic_key = Expr.LVar "#symbolic_key"

let symbolic_singleton () =
  List.iter
    (fun typ ->
      let context = symbolic_context typ in
      let heap = Heap.init () in
      (* Logical cell production has no insertion provenance. Singleton order
         must be derived, not stamped onto this original frame. *)
      Heap.set heap loc_name
        (Fields.add_abstract symbolic_key (Expr.num 7.) Fields.empty)
        (Some (Expr.ESet [ symbolic_key ])) (Some metadata);
      let before = snapshot heap in
      let expected_keys = Expr.EList [ symbolic_key ] in
      check "typed singleton enumeration"
        (snd (action ~context heap getAllProps [ loc ])
        = [ loc; expected_keys ]);
      let remainder, outs = consume ~context heap in
      check "symbolic witness and value preserved"
        (outs = [ expected_keys; Expr.EList [ Expr.num 7. ] ]);
      check "consume/enumeration does not promote original history"
        (snapshot heap = before);
      let restored = produce ~context remainder (List.hd outs) (List.nth outs 1) in
      check "roundtrip enumeration remains the symbolic key"
        (snd (action ~context restored getAllProps [ loc ])
        = [ loc; expected_keys ]);
      check "roundtrip retains metadata"
        (snd (action ~context restored getMetadata [ loc ]) = [ loc; metadata ]))
    [ Type.Utf16Type; Type.StringType ]

let symbolic_rejections () =
  let heap = Heap.init () in
  let before = snapshot heap in
  let ks = Expr.EList [ symbolic_key ] in
  let vs = Expr.EList [ Expr.num 7. ] in
  List.iter
    (fun context ->
      check "untyped and non-string singleton keys rejected"
        (Memory.produce aOrderedFields heap context [ loc; ks; vs ] = []);
      let invalid = Heap.init () in
      Heap.set invalid loc_name
        (Fields.add_abstract symbolic_key (Expr.num 7.) Fields.empty)
        (Some (Expr.ESet [ symbolic_key ])) (Some metadata);
      check "consumer cannot admit a non-string singleton"
        (match Memory.consume aOrderedFields invalid context [ loc ] with
        | [ { Branch.value = Error _; _ } ] -> true
        | _ -> false))
    [ pc (); symbolic_context Type.NumberType; symbolic_context Type.BooleanType ];
  let context = symbolic_context Type.Utf16Type in
  List.iter
    (fun (ks, vs) ->
      check "typed key does not bypass witness validity"
        (Memory.produce aOrderedFields heap context [ loc; ks; vs ] = []))
    [
      (ks, Expr.EList [ Expr.Lit Literal.Nono ]);
      (ks, Expr.EList [ Expr.LVar "#possibly_absent" ]);
      (Expr.EList [ symbolic_key; symbolic_key ], values);
      (Expr.EList [ symbolic_key; key "other" ], values);
    ];
  check "failed symbolic production preserves heap" (snapshot heap = before);
  let occupied = make () in
  let occupied_before = snapshot occupied in
  check "symbolic witness cannot overwrite an owned footprint"
    (Memory.produce aOrderedFields occupied context [ loc; ks; vs ] = []);
  check "overlap rejection preserves original"
    (snapshot occupied = occupied_before)

let () =
  Alcotest.run "Ordered fields"
    [
      ( "resource",
        List.map
          (fun (name, f) -> Alcotest.test_case name `Quick f)
          [
            ("real consume/produce roundtrip", roundtrip);
            ("runtime deletion/reinsertion", reinsert);
            ("incomplete footprints", incomplete);
            ("complete exposed absence", exposed_absence);
            ("overlap rejected", overlap);
            ("invalid witnesses", malformed);
            ("empty and metadata-only", empty_and_metadata);
            ("unknown provenance and admission", unknown_and_actions);
            ("copy and serialization", copying);
            ("complete frame assertion roundtrip", frame_export);
            ("frame export after mutation", frame_export_mutation);
            ("conservative frame export", conservative_export);
            ("typed symbolic singleton roundtrip", symbolic_singleton);
            ("symbolic witness and ownership rejection", symbolic_rejections);
          ] );
    ]
