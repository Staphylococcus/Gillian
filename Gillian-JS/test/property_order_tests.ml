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

let () =
  Alcotest.run "Property order"
    [
      ( "order",
        [
          ("keys", `Quick, order);
          ("symbolic transition", `Quick, heap_transition);
          ("semantic lookup", `Quick, semantic_lookup);
          ("typed keys", `Quick, typed_keys);
        ] );
    ]
