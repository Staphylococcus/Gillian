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

let sequence_keys = Expr.LVar "#sequence_keys"
let sequence_values = Expr.LVar "#sequence_values"

let sequence_context () =
  let context = pc () in
  List.iter
    (fun name -> Gillian.Symbolic.Type_env.update context.gamma name Type.ListType)
    [ "#sequence_keys"; "#sequence_values" ];
  Gillian.Symbolic.Pure_context.extend context.pfs
    (Expr.BinOp (UnOp (LstLen, sequence_keys), Equal,
                 UnOp (LstLen, sequence_values)));
  context

let sequence_make context =
  let heap = Heap.init () in
  Heap.set heap loc_name Fields.empty None (Some metadata);
  produce ~context heap sequence_keys sequence_values

let sequence_roundtrip () =
  let context = sequence_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  check "whole sequence actual enumeration"
    (snd (action ~context heap getAllProps [ loc ]) = [ loc; sequence_keys ]);
  let remainder, outs = consume ~context heap in
  check "whole sequence consume preserves both witnesses"
    (outs = [ sequence_keys; sequence_values ]);
  check "whole sequence consumption is persistent" (snapshot heap = before);
  check "whole sequence consumption leaves metadata only"
    (Heap.get remainder loc_name = Some ((Fields.empty, None), Some metadata));
  let restored = produce ~context remainder (List.hd outs) (List.nth outs 1) in
  check "whole sequence production preserves metadata"
    (snd (action ~context restored getMetadata [ loc ]) = [ loc; metadata ]);
  Heap.clean_up restored;
  check "cleanup retains complete ownership"
    (snd (action ~context restored getAllProps [ loc ]) = [ loc; sequence_keys ]);
  Heap.is_well_formed restored

let sequence_export_copy () =
  let context = sequence_context () in
  let heap = sequence_make context in
  let assertions = Heap.assertions heap in
  check "export contains whole witness, not raw empty cells"
    (List.exists
       (function Asrt.CorePred (name, [ l ], [ ks; vs ]) ->
          name = aOrderedFields && l = loc && ks = sequence_keys && vs = sequence_values
        | _ -> false) assertions);
  let restore = List.fold_left
      (fun h -> function
        | Asrt.CorePred (name, ins, outs) -> (match Memory.produce name h context (ins @ outs) with
            | [ { Branch.value = h; _ } ] -> h
            | _ -> Alcotest.fail "sequence frame restoration failed")
        | _ -> Alcotest.fail "unexpected exported assertion") (Heap.init ()) assertions in
  let serialized = match Heap.of_yojson (Heap.to_yojson heap) with
    | Ok h -> h | Error text -> Alcotest.fail text in
  List.iter (fun h ->
      check "copy/JSON/frame preserve arbitrary sequence"
        (snd (action ~context h getAllProps [ loc ]) = [ loc; sequence_keys ]);
      check "witness variables remain visible to substitution"
        (Var.Set.mem "#sequence_keys" (Heap.lvars h)
         && Var.Set.mem "#sequence_values" (Heap.lvars h));
      Heap.is_well_formed h)
    [ Heap.copy heap; serialized; restore ]

let sequence_substitution () =
  let context = sequence_context () in
  let substitute ks vs =
    let heap = sequence_make context in
    let subst = Gillian.Symbolic.Subst.init
        [ sequence_keys, ks; sequence_values, vs ] in
    Heap.substitution_in_place subst heap; heap
  in
  let h = substitute (keys [ "z"; "a" ]) values in
  check "concrete substitution retains supplied order" (has_order h [ "z"; "a" ]);
  let remainder, out = consume h in
  let exposed = produce remainder (List.hd out) (List.nth out 1) in
  check "valid concrete witness can become exposed again"
    (snd (action exposed getCell [ loc; key "z" ]) = [ loc; key "z"; Expr.num 1. ]);
  List.iter (fun (ks, vs) -> reject_consume (substitute ks vs))
    [ keys [ "z"; "z" ], values;
      keys [ "z" ], values;
      keys [ "10"; "2" ], values;
      keys [ "z"; "a" ], Expr.EList [ Expr.num 1.; Expr.Lit Literal.Nono ] ];
  let child = Expr.ALoc "#loc_sequence_child" in
  let h = substitute (keys [ "z" ]) (Expr.EList [ child ]) in
  check "child identities remain visible to freshness"
    (Var.Set.mem "#loc_sequence_child" (Heap.alocs h))

let sequence_aliases () =
  let context = sequence_context () in
  let target = "#loc_sequence_target" in
  let h = sequence_make context in
  Heap.merge_loc h loc_name loc_name;
  check "identity substitution cannot delete ownership" (Heap.get_ordered h loc_name <> None);
  Heap.merge_loc h target loc_name;
  check "fresh location substitution moves whole ownership"
    (Heap.get_ordered h target = Some (sequence_keys, sequence_values)
     && not (Heap.has_loc h loc_name));
  let collides expose =
    let h = sequence_make context in
    expose h;
    let before = snapshot h in
    let rejected = try Heap.merge_loc h target loc_name; false
      with Gillian.Utils.Exceptions.Unsupported _ -> true in
    check "aliasing exclusive ownership rejects" rejected;
    check "alias rejection does not drop either footprint" (before = snapshot h)
  in
  collides (fun h -> Heap.set_ordered h target sequence_keys sequence_values);
  collides (fun h -> Heap.init_object h target None);
  collides (fun h -> Heap.set h target (Fields.add_abstract (key "z") (Expr.num 3.) Fields.empty) None None);
  let h = sequence_make context in
  Heap.set h target Fields.empty None (Some metadata);
  Heap.merge_loc h target loc_name;
  check "metadata-only alias frames without duplicate cells"
    (Heap.get_ordered h target = Some (sequence_keys, sequence_values)
     && Heap.get_met h target = Some metadata)

let sequence_exclusivity () =
  let context = sequence_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  List.iter (fun (name, args) ->
      let rejected = try ignore (action ~context heap name args); false
        with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError text) ->
          text = "Unsupported ordered fields: operation requires exposed cells." in
      check (name ^ " cannot bypass opaque ownership") rejected;
      check "unsupported action retains original footprint" (snapshot heap = before))
    [ getCell, [ loc; key "z" ]; setCell, [ loc; key "z"; Expr.num 4. ];
      delCell, [ loc; key "z" ]; setProps, [ loc; Expr.ESet [] ];
      delProps, [ loc; Expr.ESet [] ]; delObj, [ loc ];
      Legacy.ga_to_setter aCell, [ loc; key "z"; Expr.Lit Literal.Nono ] ];
  check "second whole sequence cannot overlap"
    (Memory.produce aOrderedFields heap context [ loc; sequence_keys; sequence_values ] = []);
  reject_produce heap (keys [ "z"; "a" ]) values;
  let occupied = make () in
  check "whole sequence cannot overlap exposed ownership"
    (Memory.produce aOrderedFields occupied context [ loc; sequence_keys; sequence_values ] = []);
  check "whole sequence is not discarded by rejection" (snapshot heap = before)

let sequence_shape_rejections () =
  let heap = Heap.init () in
  check "untyped list witnesses cannot create whole fields"
    (Memory.produce aOrderedFields heap (pc ()) [ loc; sequence_keys; sequence_values ] = []);
  let context = sequence_context () in
  List.iter (fun (ks, vs) ->
      check "known malformed fragment cannot hide in opaque witness"
        (Memory.produce aOrderedFields heap context [ loc; ks; vs ] = []))
    [ keys [ "z"; "z" ], sequence_values;
      keys [ "10"; "2" ], sequence_values;
      Expr.num 1., sequence_values;
      sequence_keys, Expr.EList [ Expr.Lit Literal.Nono ] ]

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
            ("whole sequence roundtrip and metadata", sequence_roundtrip);
            ("whole sequence export copy serialization", sequence_export_copy);
            ("whole sequence value substitution", sequence_substitution);
            ("whole sequence location aliases", sequence_aliases);
            ("whole sequence exclusive action guards", sequence_exclusivity);
            ("whole sequence known-shape rejection", sequence_shape_rejections);
          ] );
    ]
