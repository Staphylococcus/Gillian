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

let () =
  Alcotest.run "Property order"
    [
      ( "order",
        [
          ("keys", `Quick, order);
          ("symbolic transition", `Quick, heap_transition);
          ("semantic lookup", `Quick, semantic_lookup);
        ] );
    ]
