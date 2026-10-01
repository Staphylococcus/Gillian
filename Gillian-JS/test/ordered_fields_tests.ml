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

let sequence_index = Expr.LVar "#sequence_index"

let indexed_context ?(lower = true) ?(upper = true) () =
  let context = sequence_context () in
  Gillian.Symbolic.Type_env.update context.gamma "#sequence_index" Type.IntType;
  let add = Gillian.Symbolic.Pure_context.extend context.pfs in
  if lower then add (Expr.BinOp (Expr.zero_i, ILessThanEqual, sequence_index));
  if upper then add (Expr.BinOp (sequence_index, ILessThan, UnOp (LstLen, sequence_keys)));
  context

let selected_key = Expr.BinOp (sequence_keys, LstNth, sequence_index)
let selected_value = Expr.BinOp (sequence_values, LstNth, sequence_index)

let sequence_indexed_read () =
  let context = indexed_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  check "total action accepts resource-backed selected key without extra key facts"
    (Legacy.prepare_total_action getCell heap context.pfs context.gamma
       [ loc; selected_key ] = [ loc; selected_key ]);
  (match Legacy.execute_action getCell heap context.pfs context.gamma [ loc; selected_key ] with
   | Ok [ (after, outputs, learned, _) ] ->
       check "actual lookup returns paired value at the same arbitrary index"
         (outputs = [ loc; selected_key; selected_value ]);
       check "only resource-entailed presence is learned"
         (learned = [ Expr.UnOp (Not, BinOp (selected_value, Equal, Lit Literal.Nono)) ]);
       check "read is persistent and metadata is framed"
         (snapshot after = before && Heap.get_met after loc_name = Some metadata)
   | _ -> Alcotest.fail "indexed lookup failed");
  let _, witnesses = consume ~context heap in
  check "read leaves complete resource available to checked summary"
    (witnesses = [ sequence_keys; sequence_values ])

let sequence_indexed_bounds () =
  let reject context prop =
    let heap = sequence_make context in
    let before = snapshot heap in
    let rejected = try ignore (action ~context heap getCell [ loc; prop ]); false
      with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError text) ->
        text = "Unsupported ordered fields: operation requires exposed cells." in
    check "unproved index or unrelated list cannot select an owned value" rejected;
    check "rejected read leaves ownership intact" (snapshot heap = before)
  in
  reject (indexed_context ~lower:false ()) selected_key;
  reject (indexed_context ~upper:false ()) selected_key;
  let context = indexed_context () in
  Gillian.Symbolic.Type_env.update context.gamma "#other_keys" Type.ListType;
  reject context (Expr.BinOp (LVar "#other_keys", LstNth, sequence_index));
  reject context (key "z")

let sequence_indexed_cell_consumption () =
  let context = indexed_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  let rejected = try
      ignore (Memory.consume aCell heap context [ loc; selected_key ]); false
    with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) -> true in
  check "read access does not authorize separate cell consumption" rejected;
  check "failed split retains whole ownership" (snapshot heap = before)

let sequence_indexed_known_values () =
  let context = indexed_context () in
  let heap = sequence_make context in
  let subst = Gillian.Symbolic.Subst.init
      [ sequence_values, values; sequence_index, Expr.one_i ] in
  Heap.substitution_in_place subst heap;
  let context = sequence_context () in
  Gillian.Symbolic.Pure_context.extend context.pfs
    (Expr.BinOp (UnOp (LstLen, sequence_keys), Equal, Expr.int 2));
  let prop = Expr.BinOp (sequence_keys, LstNth, Expr.one_i) in
  (match Legacy.execute_action getCell heap context.pfs context.gamma [ loc; prop ] with
   | Ok [ (_, [ _; _; value ], _, _) ] ->
       let value = Gillian.Logic.Reduction.reduce_lexpr ~pfs:context.pfs ~gamma:context.gamma value in
       check "nonempty concrete value witness selects second, not first" (value = Expr.num 2.)
   | _ -> Alcotest.fail "concrete values indexed lookup failed")

let membership_literals () =
  let store = Engine.CExprEval.CStore.init [] in
  let utf16 units = Literal.Utf16String
      (Gillian.Utils.Utf16.of_canonical (Gillian.Utils.Utf16.of_code_units units)) in
  let check_case xs value expected =
    let term = Expr.BinOp (Lit (Literal.LList xs), LstContains, Lit value) in
    check "concrete membership uses value identity"
      (Engine.CExprEval.evaluate_expr store term = Literal.Bool expected);
    check "reduction agrees with concrete membership"
      (Gillian.Logic.Reduction.reduce_lexpr term = Expr.bool expected);
    check "direct SMT agrees with concrete membership"
      (not (Smt.is_sat (Expr.Set.singleton
              (Expr.BinOp (term, ValueEqual, Expr.bool (not expected))))
              (Gillian.Symbolic.Type_env.as_hashtbl
                 (Gillian.Symbolic.Type_env.init ()))))
  in
  List.iter (fun (xs, value, expected) -> check_case xs value expected)
    [ [], Literal.Null, false;
      [ utf16 [ 0; 0xd800 ] ], utf16 [ 0; 0xd800 ], true;
      [ utf16 [ 0xd800 ] ], utf16 [ 0xdc00 ], false;
      [ Literal.String "z" ], utf16 [ 122 ], false;
      [ Literal.Num nan ], Literal.Num nan, true;
      [ Literal.Num 0. ], Literal.Num (-0.), false;
      [ Literal.LList [ Literal.Num nan; Literal.Num (-0.) ] ],
        Literal.LList [ Literal.Num nan; Literal.Num (-0.) ], true;
      [ Literal.LList [] ], Literal.LList [ Literal.Null ], false ]

let membership_domains () =
  let context = sequence_context () in
  let member = Expr.LVar "#domain_member" in
  Gillian.Symbolic.Type_env.update context.gamma "#domain_member" Type.Utf16Type;
  let evaluate = Gillian.Logic.Reduction.reduce_lexpr
      ~pfs:context.pfs ~gamma:context.gamma in
  let proves condition = Gillian.Logic.FOSolver.check_entailment
      Gillian.Utils.Containers.SS.empty context.pfs [ condition ] context.gamma in
  let accepts term = try
      Engine.Totality.check_expression ~proof:true ~proves ~evaluate
        ~require:(fun _ condition -> if not (proves condition) then failwith "domain") term;
      true
    with Failure message when message = "domain" -> false in
  check "membership accepts typed symbolic lists and keys"
    (accepts (Expr.BinOp (sequence_keys, LstContains, member)));
  check "membership rejects a non-list operand"
    (not (accepts (Expr.BinOp (Expr.num 0., LstContains, member))));
  check "logical sets are not values stored in GIL lists"
    (not (accepts (Expr.BinOp (sequence_keys, LstContains, Expr.ESet []))))

let membership_symbolic () =
  let context = sequence_context () in
  let value = Expr.LVar "#member" in
  Gillian.Symbolic.Type_env.update context.gamma "#member" Type.Utf16Type;
  let contains list = Expr.BinOp (list, LstContains, value) in
  let appended = Expr.NOp (LstCat, [ sequence_keys; Expr.EList [ value ] ]) in
  let sat fs = Smt.is_sat (Expr.Set.of_list fs)
      (Gillian.Symbolic.Type_env.as_hashtbl context.gamma) in
  check "appended member occurs for arbitrary preceding length"
    (not (sat [ Expr.UnOp (Not, contains appended) ]));
  check "absence is satisfiable for an empty sequence"
    (sat [ Expr.BinOp (sequence_keys, Equal, Expr.EList []);
           Expr.UnOp (Not, contains sequence_keys) ]);
  check "presence is satisfiable for a nonempty sequence"
    (sat [ contains sequence_keys ]);
  check "membership and absence are contradictory"
    (not (sat [ contains sequence_keys; Expr.UnOp (Not, contains sequence_keys) ]))

let absent_key = Expr.LVar "#absent_key"
let absence_context ?(typed = true) ?(keys = sequence_keys) () =
  let context = sequence_context () in
  if typed then Gillian.Symbolic.Type_env.update context.gamma
      "#absent_key" Type.Utf16Type;
  Gillian.Symbolic.Pure_context.extend context.pfs
    (Expr.UnOp (Not, BinOp (keys, LstContains, absent_key)));
  context

let sequence_absent_read () =
  let context = absence_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  check "total lookup requires only proved typed absence"
    (Legacy.prepare_total_action getCell heap context.pfs context.gamma
       [ loc; absent_key ] = [ loc; absent_key ]);
  (match Legacy.execute_action getCell heap context.pfs context.gamma [ loc; absent_key ] with
   | Ok [ (after, out, facts, _) ] ->
       check "complete sequence absence returns internal none"
         (out = [ loc; absent_key; Expr.Lit Literal.Nono ] && facts = []);
       check "lookup preserves exact sequence and metadata"
         (snapshot after = before && Heap.get_met after loc_name = Some metadata)
   | _ -> Alcotest.fail "absent lookup failed");
  check "lookup leaves both witnesses consumable"
    (snd (consume ~context heap) = [ sequence_keys; sequence_values ])

let reject_absent context prop =
  let heap = sequence_make context in
  let before = snapshot heap in
  let rejected = try ignore (action ~context heap getCell [ loc; prop ]); false
    with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) -> true in
  check "absence requires proved nonmembership in owned keys" rejected;
  check "rejection retains complete ownership" (snapshot heap = before)

let absence_no_fact () =
  let context = sequence_context () in
  Gillian.Symbolic.Type_env.update context.gamma "#absent_key" Type.Utf16Type;
  reject_absent context absent_key

let absence_wrong_list () =
  let context = absence_context ~keys:(Expr.LVar "#other_keys") () in
  Gillian.Symbolic.Type_env.update context.gamma "#other_keys" Type.ListType;
  reject_absent context absent_key

let absence_present () =
  let context = sequence_context () in
  Gillian.Symbolic.Type_env.update context.gamma "#absent_key" Type.Utf16Type;
  Gillian.Symbolic.Pure_context.extend context.pfs
    (Expr.BinOp (sequence_keys, LstContains, absent_key));
  reject_absent context absent_key

let absence_nonkey () =
  reject_absent (absence_context ~typed:false ()) absent_key;
  let context = absence_context ~typed:false () in
  Gillian.Symbolic.Type_env.update context.gamma "#absent_key" Type.NumberType;
  reject_absent context absent_key

let absence_no_cell_split () =
  let context = absence_context () in
  let heap = sequence_make context in
  let before = snapshot heap in
  let rejected = try ignore (Memory.consume aCell heap context [ loc; absent_key ]); false
    with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) -> true in
  check "absence read does not duplicate a separately consumable cell" rejected;
  check "failed split leaves whole resource" (snapshot heap = before)

let ukey s = Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical s))
let ukeys xs = Expr.EList (List.map ukey xs)

let insertion_position_literals () =
  let store = Engine.CExprEval.CStore.init [] in
  let gamma = Gillian.Symbolic.Type_env.as_hashtbl (Gillian.Symbolic.Type_env.init ()) in
  List.iter (fun (names, name, expected) ->
    let term = Expr.BinOp (ukeys names, KeyInsertIndex, ukey name) in
    check "concrete exact insertion index" (Engine.CExprEval.evaluate_expr store term = Literal.Int (Z.of_int expected));
    check "reducer agrees with concrete insertion" (Gillian.Logic.Reduction.reduce_lexpr term = Expr.int expected);
    check "SMT agrees with exact numeric/name classification"
      (not (Smt.is_sat (Expr.Set.singleton (Expr.UnOp (Not, BinOp (term, Equal, Expr.int expected)))) gamma)))
    [ [], "0", 0; [], "z", 0;
      ["2"; "10"; "z"; "a"], "1", 0;
      ["2"; "10"; "z"; "a"], "3", 1;
      ["2"; "10"; "z"; "a"], "11", 2;
      ["2"; "10"; "z"; "a"], "b", 4;
      ["0"; "2"; "4294967294"; "z"], "4294967293", 2;
      ["0"; "2"; "z"], "4294967294", 2;
      ["0"; "2"; "z"], "4294967295", 3;
      ["0"; "2"; "z"], "01", 3;
      ["0"; "2"; "z"], "-0", 3;
      ["z"], "__proto__", 1;
      ["z"], "", 1;
      ["z"], Gillian.Utils.Utf16.of_code_units [0xd800], 1 ]

let insertion_literal_values () =
  let store = Engine.CExprEval.CStore.init [] in
  let xs = Literal.LList [ Literal.Num nan; Literal.Num (-0.) ] in
  let v = Literal.LList [ Literal.Null ] in
  List.iter (fun (i, expected) ->
    let term = Expr.NOp (LstInsert, [ Lit xs; Expr.int i; Lit v ]) in
    check "concrete insertion retains exact value identity"
      (Literal.same_value (Engine.CExprEval.evaluate_expr store term) (Literal.LList expected));
    let wrong = Expr.UnOp (Not, BinOp (term, ValueEqual, Lit (Literal.LList expected))) in
    check "SMT insertion preserves NaN signed-zero nested values"
      (not (Smt.is_sat (Expr.Set.singleton wrong)
        (Gillian.Symbolic.Type_env.as_hashtbl (Gillian.Symbolic.Type_env.init ())))))
    [ 0, [v; Literal.Num nan; Literal.Num (-0.)];
      1, [Literal.Num nan; v; Literal.Num (-0.)];
      2, [Literal.Num nan; Literal.Num (-0.); v] ];
  List.iter (fun i ->
    let rejected = try ignore (Engine.CExprEval.evaluate_expr store
      (NOp (LstInsert, [Lit xs; Expr.int i; Lit v]))); false
      with Engine.CExprEval.EvaluationError _ -> true in
    check "concrete invalid position rejects" rejected) [-1; 3]

let insertion_symbolic_lengths () =
  let c = sequence_context () in
  let i = Expr.LVar "#insert_at" and v = Expr.LVar "#insert_value" in
  Gillian.Symbolic.Type_env.update c.gamma "#insert_at" Type.IntType;
  Gillian.Symbolic.Type_env.update c.gamma "#insert_value" Type.Utf16Type;
  let term = Expr.NOp (LstInsert, [sequence_keys; i; v]) in
  let fs = [ Expr.BinOp (Expr.zero_i, ILessThanEqual, i);
    Expr.BinOp (i, ILessThanEqual, UnOp (LstLen, sequence_keys));
    Expr.UnOp (Not, BinOp (UnOp (LstLen, term), Equal,
      BinOp (UnOp (LstLen, sequence_keys), IPlus, Expr.one_i))) ] in
  check "exact structural insertion adds one at any finite list length"
    (not (Smt.is_sat (Expr.Set.of_list fs) (Gillian.Symbolic.Type_env.as_hashtbl c.gamma)))

let insertion_key_representation () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter (fun (xs, result) ->
    let term = Expr.UnOp (LstAllUtf16, xs) in
    check "concrete uniform representation" (Engine.CExprEval.evaluate_expr store term = Literal.Bool result);
    check "SMT uniform representation"
      (not (Smt.is_sat (Expr.Set.singleton (Expr.BinOp (term, ValueEqual, Expr.bool (not result))))
        (Gillian.Symbolic.Type_env.as_hashtbl (Gillian.Symbolic.Type_env.init ())))))
    [Expr.EList [], true; ukeys ["0"; "z"], true;
      Expr.EList [ukey "z"; key "a"], false; Expr.EList [Expr.Lit Literal.Null], false]

let insertion_quantifier_names () =
  let gamma = Gillian.Symbolic.Type_env.init () in
  let xs = Expr.LVar "all_u16_index" in
  Gillian.Symbolic.Type_env.update gamma "all_u16_index" Type.ListType;
  let fs = [ Expr.BinOp (xs, Equal, ukeys ["z"]);
    Expr.UnOp (Not, UnOp (LstAllUtf16, xs)) ] in
  check "UTF16 universal binder cannot capture a caller list name"
    (not (Smt.is_sat (Expr.Set.of_list fs) (Gillian.Symbolic.Type_env.as_hashtbl gamma)))

let insertion_context () =
  let c = absence_context () in
  Gillian.Symbolic.Pure_context.extend c.pfs (Expr.UnOp (LstAllUtf16, sequence_keys));
  c

let sequence_runtime_insert () =
  let c = insertion_context () in
  let heap = sequence_make c in
  let before = snapshot heap in
  let args = [loc; absent_key; Expr.Lit Literal.Null] in
  check "total setter accepts proved complete insertion"
    (Legacy.prepare_total_action setCell heap c.pfs c.gamma args = args);
  match Legacy.execute_action setCell heap c.pfs c.gamma args with
  | Ok [ (after, [], facts, []) ] ->
      let position = Expr.BinOp (sequence_keys, KeyInsertIndex, absent_key) in
      check "real setter derives paired key/value witnesses"
        (Heap.get_ordered after loc_name = Some
           (Expr.NOp (LstInsert, [sequence_keys; position; absent_key]),
            Expr.NOp (LstInsert, [sequence_values; position; Expr.Lit Literal.Null])));
      check "input branch and metadata preserved"
        (snapshot heap = before && Heap.get_met after loc_name = Some metadata);
      check "transfer derives exactly four justified facts" (List.length facts = 4)
  | _ -> Alcotest.fail "complete insertion failed"

let insertion_reject_guards () =
  let reject c prop v =
    let heap = sequence_make c in
    let before = snapshot heap in
    let rejected = try ignore (Legacy.execute_action setCell heap c.pfs c.gamma [loc;prop;v]); false
      with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) -> true in
    check "invalid insertion rejected" rejected;
    check "failed insertion preserves input" (snapshot heap = before)
  in
  reject (absence_context ()) absent_key (Expr.Lit Literal.Null);
  reject (sequence_context ()) absent_key (Expr.Lit Literal.Null);
  reject (insertion_context ()) absent_key (Expr.Lit Literal.Nono);
  reject (insertion_context ()) (key "legacy") (Expr.Lit Literal.Null);
  reject (insertion_context ()) absent_key (Expr.ESet []);
  let c = sequence_context () in
  Gillian.Symbolic.Type_env.update c.gamma "#absent_key" Type.Utf16Type;
  Gillian.Symbolic.Pure_context.extend c.pfs (Expr.UnOp (LstAllUtf16, sequence_keys));
  Gillian.Symbolic.Pure_context.extend c.pfs (Expr.BinOp (sequence_keys, LstContains, absent_key));
  reject c absent_key (Expr.Lit Literal.Null)

let insertion_no_logical_production () =
  let c = insertion_context () in
  let heap = sequence_make c in
  let before = snapshot heap in
  let rejected = try Memory.produce aCell heap c [ loc; absent_key; Expr.Lit Literal.Null ] = []
    with Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _) -> true in
  check "raw Cell production cannot mutate packed ownership" rejected;
  check "raw producer leaves packed resource" (snapshot heap = before)

let insertion_total_domains () =
  let c = insertion_context () in
  let evaluate = Gillian.Logic.Reduction.reduce_lexpr ~pfs:c.pfs ~gamma:c.gamma in
  let proves f = Gillian.Logic.FOSolver.check_entailment Gillian.Utils.Containers.SS.empty c.pfs [f] c.gamma in
  let accepts term = try Engine.Totality.check_expression ~proof:true ~proves ~evaluate
    ~require:(fun _ f -> if not (proves f) then failwith "domain") term; true
    with Failure message when message = "domain" -> false in
  check "exact primitive accepts UTF16/list domain" (accepts (Expr.BinOp (sequence_keys, KeyInsertIndex, absent_key)));
  check "key position rejects Number key" (not (accepts (Expr.BinOp (sequence_keys, KeyInsertIndex, Expr.num 1.))));
  check "insertion rejects negative bound" (not (accepts (Expr.NOp (LstInsert, [ukeys []; Expr.int (-1); Expr.Lit Literal.Null]))));
  check "insertion rejects greater-than-length bound" (not (accepts (Expr.NOp (LstInsert, [ukeys []; Expr.int 1; Expr.Lit Literal.Null]))));
  check "insertion accepts exact integer endpoint" (accepts (Expr.NOp (LstInsert, [ukeys []; Expr.int 0; Expr.Lit Literal.Null])))

let insertion_symbolic_bounds () =
  let c = insertion_context () in
  let position = Expr.BinOp (sequence_keys, KeyInsertIndex, absent_key) in
  let bounds = [ Expr.BinOp (Expr.zero_i, ILessThanEqual, position);
    Expr.BinOp (position, ILessThanEqual, UnOp (LstLen, sequence_keys)) ] in
  List.iter (fun bound ->
    check "typed structural position bound reduces without recursive SMT"
      (Gillian.Logic.Reduction.reduce_lexpr ~gamma:c.gamma bound = Expr.true_)) bounds;
  List.iter (fun outside ->
    check "negated endpoint bound reduces after comparison normalization"
      (Gillian.Logic.Reduction.reduce_lexpr ~gamma:c.gamma outside = Expr.false_))
    [ Expr.BinOp (position, ILessThan, Expr.zero_i);
      Expr.BinOp (UnOp (LstLen, sequence_keys), ILessThan, position) ];
  check "total insertion accepts symbolic position without assumed bounds"
    (let evaluate = Gillian.Logic.Reduction.reduce_lexpr ~pfs:c.pfs ~gamma:c.gamma in
     let proves f = Gillian.Logic.FOSolver.check_entailment Gillian.Utils.Containers.SS.empty c.pfs [f] c.gamma in
     try Engine.Totality.check_expression ~proof:true ~proves ~evaluate
       ~require:(fun _ f -> if not (proves f) then failwith "bound")
       (Expr.NOp (LstInsert, [sequence_keys; position; Expr.Lit Literal.Null])); true
     with Failure message when message = "bound" -> false)

let insertion_bound_domains () =
  let c = insertion_context () in
  let p = Expr.BinOp (sequence_keys, KeyInsertIndex, absent_key) in
  let lower = Expr.BinOp (Expr.zero_i, ILessThanEqual, p) in
  let reduce gamma e = Gillian.Logic.Reduction.reduce_lexpr ~gamma e in
  let unknown = Gillian.Symbolic.Type_env.init () in
  check "missing list/key types cannot authorize a bound" (reduce unknown lower <> Expr.true_);
  let list_only = Gillian.Symbolic.Type_env.init () in
  Gillian.Symbolic.Type_env.update list_only "#sequence_keys" Type.ListType;
  check "missing key type cannot authorize a bound" (reduce list_only lower <> Expr.true_);
  let other = Expr.LVar "#other_keys" in
  Gillian.Symbolic.Type_env.update c.gamma "#other_keys" Type.ListType;
  check "unrelated length is not a position bound"
    (reduce c.gamma (Expr.BinOp (p, ILessThanEqual, UnOp (LstLen, other))) <> Expr.true_);
  check "strict endpoint is not implied"
    (reduce c.gamma (Expr.BinOp (Expr.zero_i, ILessThan, p)) <> Expr.true_);
  let partial = Expr.UnOp (Car, Expr.EList []) in
  check "shortcut does not erase a partial list input"
    (try ignore (reduce c.gamma (Expr.BinOp (Expr.zero_i, ILessThanEqual,
       Expr.BinOp (partial, KeyInsertIndex, absent_key)))); false
     with Gillian.Logic.Reduction.ReductionException _ -> true);
  let wrong = Expr.BinOp (sequence_keys, KeyInsertIndex, Expr.num 1.) in
  check "Number key is not UTF16"
    (try reduce c.gamma (Expr.BinOp (Expr.zero_i, ILessThanEqual, wrong)) <> Expr.true_
     with Failure message -> String.starts_with ~prefix:"TYPE ERROR:" message)

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
            ("whole sequence arbitrary indexed read", sequence_indexed_read);
            ("whole sequence index bounds and identity", sequence_indexed_bounds);
            ("whole sequence no separate cell consumption", sequence_indexed_cell_consumption);
            ("whole sequence selected concrete value", sequence_indexed_known_values);
            ("exact key insertion positions", insertion_position_literals);
            ("insertion exact values", insertion_literal_values);
            ("insertion arbitrary list length", insertion_symbolic_lengths);
            ("uniform key representation", insertion_key_representation);
            ("capture-free UTF16 quantifier", insertion_quantifier_names);
            ("actual complete-sequence insertion", sequence_runtime_insert);
            ("insertion ownership rejection", insertion_reject_guards);
            ("insertion no raw logical production", insertion_no_logical_production);
            ("insertion total domains", insertion_total_domains);
            ("symbolic insertion position bounds", insertion_symbolic_bounds);
            ("insertion bound domains", insertion_bound_domains);
            ("membership literal identity", membership_literals);
            ("membership exact symbolic sequence", membership_symbolic);
            ("membership total domains", membership_domains);
            ("whole sequence absent read", sequence_absent_read);
            ("absence requires nonmembership", absence_no_fact);
            ("absence requires owned list", absence_wrong_list);
            ("presence cannot authorize absence", absence_present);
            ("absence requires string key", absence_nonkey);
            ("absence cannot split ownership", absence_no_cell_split);
          ] );
    ]
