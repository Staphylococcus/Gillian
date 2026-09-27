open Gillian.Gil_syntax
module Fields = Semantics.SFVL

let name value = Expr.Lit (Literal.String value)
let value = Expr.Lit (Literal.Num 1.)

let names fields =
  Fields.ordered_field_names fields
  |> List.map (function
       | Expr.Lit (Literal.String name) -> name
       | _ -> assert false)

let check expected fields =
  Alcotest.(check (list string)) "property order" expected (names fields)

let order () =
  let fields =
    List.fold_left
      (fun f key -> Fields.add (name key) value f)
      Fields.empty
      [ "z"; "a"; "10"; "2"; "01"; "4294967295"; "4294967294" ]
  in
  check [ "2"; "10"; "4294967294"; "z"; "a"; "01"; "4294967295" ] fields;
  check
    [ "2"; "10"; "4294967294"; "z"; "a"; "01"; "4294967295" ]
    (Fields.add (name "z") (Expr.LVar "symbolic") fields);
  let left, right =
    Fields.partition (fun key _ -> key = name "a" || key = name "2") fields
  in
  check (names fields) (Fields.union left right);
  let recreated =
    Fields.add (name "z") value
      (Fields.add (name "z") (Expr.Lit Literal.Nono) fields)
  in
  check [ "2"; "10"; "4294967294"; "a"; "01"; "4294967295"; "z" ] recreated;
  let restored =
    match Fields.of_yojson (Fields.to_yojson fields) with
    | Ok f -> f
    | Error e -> failwith e
  in
  check (names fields) restored

let heap_transition () =
  let heap = Semantics.SHeap.init () in
  Semantics.SHeap.init_object heap "object" None;
  List.iter
    (fun key -> Semantics.SHeap.set_fv_pair heap "object" (name key) value)
    [ "z"; "a" ];
  Semantics.SHeap.set_fv_pair heap "object" (name "z") (Expr.LVar "symbolic");
  let fields =
    match Semantics.SHeap.get heap "object" with
    | Some ((f, _), _) -> f
    | None -> assert false
  in
  check [ "z"; "a" ] fields;
  Semantics.SHeap.set_fv_pair heap "object" (name "z") value;
  let fields =
    match Semantics.SHeap.get heap "object" with
    | Some ((f, _), _) -> f
    | None -> assert false
  in
  check [ "z"; "a" ] fields

let semantic_lookup () =
  let fields =
    List.fold_left
      (fun fields key -> Fields.add (name key) value fields)
      Fields.empty
      [ "a"; "b"; "c"; "d"; "e"; "f"; "g" ]
  in
  List.iter
    (fun key ->
      let result =
        Fields.get_first (fun field -> Expr.equal field (name key)) fields
      in
      Alcotest.(check bool)
        ("find " ^ key) true
        (match result with
        | Some (field, _) -> Expr.equal field (name key)
        | None -> false))
    [ "a"; "b"; "c"; "d"; "e"; "f"; "g" ];
  Alcotest.(check bool)
    "no matching key" true
    (Option.is_none (Fields.get_first (fun _ -> false) fields))

let typed_keys () =
  let module L = Literal in
  let module U = Gillian.Utils.Utf16 in
  let typed bytes = L.Utf16String (U.of_canonical (U.canonical bytes)) in
  let raw = L.String "same" and units = typed "same" in
  let concrete = Semantics.Concrete.init () in
  let execute name args =
    match Semantics.Concrete.execute_action name concrete args with
    | Ok (_, result) -> result
    | Error _ -> Alcotest.fail "Concrete heap action failed"
  in
  let open Javert_utils.JSILNames in
  let loc =
    match execute alloc [ L.Empty; L.Null ] with
    | [ loc ] -> loc
    | _ -> assert false
  in
  let set key value = ignore (execute setCell [ loc; key; value ]) in
  let get key =
    match execute getCell [ loc; key ] with
    | [ _; _; value ] -> Some value
    | _ -> None
  in
  let properties () =
    match execute getAllProps [ loc ] with
    | [ _; L.LList keys ] -> keys
    | _ -> assert false
  in
  set raw (L.Num 1.);
  set units (L.Num 2.);
  Alcotest.(check bool)
    "concrete byte and UTF-16 keys do not alias" true
    (get raw = Some (L.Num 1.) && get units = Some (L.Num 2.));
  let symbolic =
    Fields.empty
    |> Fields.add (Expr.Lit raw) (Expr.num 1.)
    |> Fields.add (Expr.Lit units) (Expr.num 2.)
  in
  Alcotest.(check bool)
    "enumeration preserves both key kinds" true
    (Fields.ordered_field_names symbolic
    = List.map (fun x -> Expr.Lit x) (properties ()));
  let pair = typed "\xf0\x9f\x98\x80"
  and escaped = typed "\xed\xa0\xbd\xed\xb8\x80" in
  set pair (L.Num 3.);
  Alcotest.(check bool)
    "equivalent JS encodings select the same property" true
    (get escaped = Some (L.Num 3.));
  let fields =
    List.fold_left
      (fun f key -> Fields.add (Expr.Lit (typed key)) value f)
      Fields.empty
      [ "z"; "a"; "10"; "2"; "01" ]
  in
  Alcotest.(check bool)
    "typed numeric keys retain JS enumeration order" true
    (Fields.ordered_field_names fields
    = List.map (fun key -> Expr.Lit (typed key)) [ "2"; "10"; "z"; "a"; "01" ])

let unknown_message =
  "Unsupported property enumeration: insertion order is unavailable after \
   logical cell production."

let rejects_unknown f =
  let rejected =
    try
      f ();
      false
    with
    | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
      msg = unknown_message
  in
  Alcotest.(check bool) "unknown order rejected specifically" true rejected

let unknown fields = rejects_unknown (fun () -> ignore (names fields))

let abstract_order () =
  let original =
    Fields.empty |> Fields.add (name "z") value |> Fields.add (name "a") value
  in
  check [ "z"; "a" ] original;
  let abstracted = Fields.add_abstract (name "z") value original in
  unknown abstracted;
  unknown (Fields.add (name "z") (Expr.num 2.) abstracted);
  (* Real deletion and recreation establishes new order; a value update cannot. *)
  check [ "a"; "z" ]
    (abstracted
    |> Fields.add (name "z") (Expr.Lit Literal.Nono)
    |> Fields.add (name "z") value);
  unknown (Fields.add_abstract (name "a") value Fields.empty)

let merged_order () =
  let known = Fields.add (name "a") value Fields.empty in
  let abstracted = Fields.add_abstract (name "a") value Fields.empty in
  List.iter unknown
    [ Fields.union known abstracted; Fields.union abstracted known ];
  let later =
    Fields.empty |> Fields.add (name "z") value |> Fields.add (name "a") value
  in
  List.iter unknown [ Fields.union known later; Fields.union later known ];
  check [ "a" ] (Fields.union known known);
  let mixed = Fields.add (name "z") value abstracted in
  let left, right = Fields.partition (fun key _ -> key = name "z") mixed in
  List.iter unknown [ Fields.union left right; Fields.union right left ];
  Alcotest.(check bool)
    "unknown is still an owned cell" true
    (Fields.get (name "a") mixed = Some value)

let substituted_order () =
  let module Subst = Gillian.Symbolic.Subst in
  let x = Expr.LVar "#x" and y = Expr.LVar "#y" and v = Expr.LVar "#v" in
  let subst = Subst.init [ (x, name "a"); (y, name "a"); (v, value) ] in
  let fields = Fields.add_abstract x v Fields.empty in
  unknown (Fields.substitution subst true fields);
  let selected = Fields.add_abstract (name "a") v Fields.empty in
  unknown (Fields.selective_substitution subst true selected);
  List.iter
    (fun (first, second) ->
      let fields =
        Fields.empty
        |> Fields.add_abstract first value
        |> Fields.add second value
      in
      unknown (Fields.substitution subst true fields))
    [ (x, y); (y, x) ]

let stored_order () =
  let module Heap = Semantics.SHeap in
  let heap = Heap.init () in
  Heap.init_object heap "object" None;
  Heap.set_fv_pair heap "object" (name "z") value;
  Heap.set_fv_pair ~abstract:true heap "object" (name "a") (Expr.LVar "#value");
  let get heap =
    match Heap.get heap "object" with
    | Some ((f, _), _) -> f
    | None -> assert false
  in
  unknown (get heap);
  let copied = Heap.copy heap in
  Heap.set_fv_pair copied "object" (name "a") value;
  unknown (get copied);
  unknown (get heap);
  Alcotest.(check bool)
    "copy preserves original symbolic value" true
    (Fields.get (name "a") (get heap) = Some (Expr.LVar "#value"));
  Heap.substitution_in_place
    (Gillian.Symbolic.Subst.init [ (Expr.LVar "#value", value) ])
    heap;
  unknown (get heap)

let serialized_order () =
  let decode json =
    match Fields.of_yojson json with
    | Ok f -> f
    | Error e -> failwith e
  in
  let known =
    Fields.empty |> Fields.add (name "z") value |> Fields.add (name "a") value
  in
  let abstracted = Fields.add_abstract (name "a") value known in
  unknown (decode (Fields.to_yojson abstracted));
  check [ "z"; "a" ] (decode (Fields.to_yojson known));
  let rec legacy = function
    | `Assoc fields ->
        `Assoc
          (List.filter_map
             (fun (k, v) ->
               if k = "order_known" then None else Some (k, legacy v))
             fields)
    | `List xs -> `List (List.map legacy xs)
    | x -> x
  in
  let old = legacy (Fields.to_yojson known) in
  Alcotest.(check bool)
    "legacy test removes provenance fields" true
    (old <> Fields.to_yojson known);
  unknown (decode old)

let memory_production () =
  let module Memory = Semantics.Legacy_symbolic in
  let open Javert_utils.JSILNames in
  let heap = Semantics.SHeap.init () in
  let loc = Expr.ALoc "#loc_order" in
  Semantics.SHeap.init_object heap "#loc_order" None;
  let pfs = Gillian.Symbolic.Pure_context.init () in
  let gamma = Gillian.Symbolic.Type_env.init () in
  let act action args =
    match Memory.execute_action action heap pfs gamma args with
    | Ok [ (_, result, _, _) ] -> result
    | _ -> Alcotest.fail "memory action did not produce exactly one outcome"
  in
  let set action key v = ignore (act action [ loc; name key; v ]) in
  ignore (act setProps [ loc; Expr.ESet [ name "z"; name "a" ] ]);
  set setCell "z" value;
  set setCell "a" value;
  let check_result expected =
    Alcotest.(check bool)
      "actual GetAllProps result" true
      (act getAllProps [ loc ] = [ loc; Expr.EList (List.map name expected) ])
  in
  check_result [ "z"; "a" ];
  set setCell "z" (Expr.num 2.);
  check_result [ "z"; "a" ];
  set setCell "z" (Expr.Lit Literal.Nono);
  set setCell "z" value;
  check_result [ "a"; "z" ];
  (* Use the same mapping as Legacy_s_memory.Modernize.produce. A stub that
     leaves aCell mapped to SetCell makes this rejection fail. *)
  let producer = Memory.ga_to_setter aCell in
  set producer "a" value;
  rejects_unknown (fun () -> ignore (act getAllProps [ loc ]));
  set setCell "a" value;
  rejects_unknown (fun () -> ignore (act getAllProps [ loc ]));
  (* Absent cells are filtered before enumeration, not treated as unknown
     present properties. A real later insertion obtains new order. *)
  set producer "a" (Expr.Lit Literal.Nono);
  check_result [ "z" ];
  set setCell "a" value;
  check_result [ "z"; "a" ]

let () =
  Alcotest.run "Property order"
    [
      ( "order",
        [
          ("keys", `Quick, order);
          ("symbolic transition", `Quick, heap_transition);
          ("semantic lookup", `Quick, semantic_lookup);
          ("typed keys", `Quick, typed_keys);
          ("abstract cell order", `Quick, abstract_order);
          ("merged provenance", `Quick, merged_order);
          ("substituted provenance", `Quick, substituted_order);
          ("heap copies and partitions", `Quick, stored_order);
          ("serialized provenance", `Quick, serialized_order);
          ("memory production mapping", `Quick, memory_production);
        ] );
    ]
