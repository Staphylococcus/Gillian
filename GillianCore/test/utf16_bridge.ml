open Simple_smt
module Codec = Gillian.Utils.Utf16
module Bridge = Smt.Utf16

let recover term =
  match Bridge.recover term with
  | Some string -> string
  | None -> Alcotest.failf "Could not recover %s" (Sexplib.Sexp.to_string term)

let all_units () =
  for unit = 0 to 0xffff do
    let string = Codec.of_code_units [ unit ] in
    let encoded = Bridge.encode string in
    let value =
      match encoded with
      | List [ Atom "seq.unit"; value ] -> Z.to_int (to_bits 16 false value)
      | _ -> Alcotest.fail "Single unit did not encode as a native unit"
    in
    if value <> unit || recover encoded <> string then
      Alcotest.failf "Bridge changed code unit %04x" unit
  done

let finite_sequences () =
  let check left right =
    let a = Codec.of_code_units left and b = Codec.of_code_units right in
    let expected = left @ right in
    let joined = a ^ b in
    if Codec.code_units joined <> expected then
      Alcotest.fail "Concrete codec did not preserve concatenation";
    let model = app_ "seq.++" [ Bridge.encode a; Bridge.encode b ] in
    if recover model <> joined || recover (Bridge.encode joined) <> joined then
      Alcotest.fail "Native sequence bridge changed a concatenation"
  in
  let boundaries =
    [
      0;
      0x7f;
      0x80;
      0x7ff;
      0x800;
      0xd7ff;
      0xd800;
      0xdbff;
      0xdc00;
      0xdfff;
      0xe000;
      0xffff;
    ]
  in
  List.iter
    (fun a -> List.iter (fun b -> check [ a ] [ b ]) boundaries)
    boundaries;
  check [] [];
  check [ 0; 65; 0xe9; 0xd83d ] [ 0xde00; 0; 0xd800; 0xffff ];
  let random = Random.State.make [| 0x16; 0xc35 |] in
  for _ = 1 to 100 do
    let units () =
      List.init (Random.State.int random 128) (fun _ ->
          Random.State.int random 0x10000)
    in
    check (units ()) (units ())
  done;
  let all = List.init 0x10000 Fun.id in
  check all (List.rev all)

let input_domain () =
  Alcotest.check_raises "raw scalar UTF-8 is not canonical CESU-8"
    (Gillian.Utils.Exceptions.Unsupported
       "UTF-16 SMT bridge requires canonical CESU-8") (fun () ->
      ignore (Bridge.encode "\xf0\x9f\x98\x80"));
  Alcotest.(check string)
    "explicit compiler-style normalization is accepted"
    (Codec.of_code_units [ 0xd83d; 0xde00 ])
    (recover (Bridge.encode (Codec.canonical "\xf0\x9f\x98\x80")));
  List.iter
    (fun malformed ->
      Alcotest.check_raises "malformed encoding does not become a JS value"
        (Gillian.Utils.Exceptions.Unsupported "Malformed WTF-8 string")
        (fun () -> ignore (Bridge.encode malformed)))
    [ "\x80"; "\xc0\x80"; "\xc2"; "\xc2A"; "\xe0\x80\x80"; "\xff" ]

let model_domain () =
  let parse = Sexplib.Sexp.of_string in
  List.iter
    (fun model ->
      Alcotest.(check (option string))
        "model cannot be silently coerced" None
        (Bridge.recover (parse model)))
    [
      "(as seq.empty (Seq (_ BitVec 8)))";
      "(as seq.empty (Seq Int))";
      "(seq.unit #xff)";
      "(seq.unit #x10000)";
      "(seq.unit #b1)";
      "(seq.unit #xzzzz)";
      "(seq.unit #x-001)";
      "(seq.unit #x+001)";
      "(seq.unit #x00_1)";
      "(seq.unit #b00000000000000_1)";
      "(seq.unit (_ bv65536 16))";
      "(seq.++)";
      "(seq.++ (seq.unit #x0001))";
      "units";
      "(seq.extract units 0 1)";
      "(let ((x)) x)";
    ];
  Alcotest.(check (list int))
    "binary model unit" [ 0xd800 ]
    (Codec.code_units (recover (parse "(seq.unit #b1101100000000000)")));
  Alcotest.(check (list int))
    "let sharing and nested concatenation" [ 0xd800; 0; 0xd800 ]
    (Codec.code_units
       (recover
          (parse
             "(let ((u (seq.unit #xd800))) (seq.++ u (seq.++ (seq.unit #x0000) \
              u)))")))

(* Reuse the existing solver library and reset between queries, as Smt does.
   Its finalizer owns this single connection. Unknown is a failed test. *)
let solver = lazy (new_solver z3)

let query declarations constraints =
  let solver = Lazy.force solver in
  ack_command solver (list [ atom "reset" ]);
  ack_command solver (set_option ":timeout" "5000");
  List.iter
    (fun name -> ack_command solver (declare name Bridge.sort))
    declarations;
  List.iter (fun term -> ack_command solver (assume term)) constraints;
  solver

let expect_result expected solver =
  match check solver with
  | result when result = expected -> ()
  | result ->
      Alcotest.failf "Expected %s, got %s" (show_result expected)
        (show_result result)

let symbolic_laws () =
  let a = atom "a" and b = atom "b" and c = atom "c" in
  let concat a b = app_ "seq.++" [ a; b ] in
  let length a = app_ "seq.len" [ a ] in
  let check constraints expected =
    expect_result expected (query [ "a"; "b"; "c" ] constraints)
  in
  check
    [ bool_not (eq (length (concat a b)) (num_add (length a) (length b))) ]
    Unsat;
  check [ bool_not (eq (concat a (concat b c)) (concat (concat a b) c)) ] Unsat;
  check [ eq (concat a b) (concat a c); bool_not (eq b c) ] Unsat;
  check [ bool_not (eq (concat a b) (concat b a)) ] Sat;
  let astral = Bridge.encode (Codec.of_code_units [ 0xd83d; 0xde00 ]) in
  check [ eq a astral; eq (length a) (int_k 1) ] Unsat;
  check [ eq a astral; eq (length a) (int_k 6) ] Unsat;
  check [ eq a astral; eq (length a) (int_k 2) ] Sat

let models () =
  let s = atom "s" and t = atom "t" in
  let length = app_ "seq.len" [ s ] in
  let first = app_ "seq.nth" [ s; int_k 0 ] in
  let fixed units = eq s (Bridge.encode (Codec.of_code_units units)) in
  let ranged lower upper =
    [
      eq length (int_k 1);
      bv_uleq (bv_k 16 (Z.of_int lower)) first;
      bv_uleq first (bv_k 16 (Z.of_int upper));
    ]
  in
  let cases =
    [
      ("empty", [ fixed [] ], [ s ]);
      ("lone-high", ranged 0xd800 0xdbff, [ s ]);
      ("lone-low", ranged 0xdc00 0xdfff, [ s ]);
      ("astral-pair", [ fixed [ 0xd83d; 0xde00 ] ], [ s ]);
      ("mixed", [ fixed [ 0; 65; 0xe9; 0xd83d; 0xde00; 0xd800; 0xffff ] ], [ s ]);
      ("arbitrary-nonempty", [ bool_not (eq s (Bridge.encode "")) ], [ s ]);
      ( "concat-order",
        [ bool_not (eq (app_ "seq.++" [ s; t ]) (app_ "seq.++" [ t; s ])) ],
        [ s; t ] );
    ]
  in
  let evidence =
    List.map
      (fun (id, constraints, expressions) ->
        let solver = query [ "s"; "t" ] constraints in
        expect_result Sat solver;
        let strings =
          List.map
            (fun expression ->
              let model = get_expr solver expression in
              let string = recover model in
              Alcotest.(check bool)
                "recovered string re-encodes to this model" true
                (to_bool
                   (get_expr solver (eq expression (Bridge.encode string))));
              ( string,
                `Assoc
                  [
                    ("smt", `String (Sexplib.Sexp.to_string model));
                    ( "units",
                      `List
                        (List.map
                           (fun unit -> `Int unit)
                           (Codec.code_units string)) );
                  ] ))
            expressions
        in
        (if id = "concat-order" then
           match List.map fst strings with
           | [ a; b ] ->
               Alcotest.(check bool)
                 "counterexample replays in concrete bytes" true
                 (a ^ b <> b ^ a)
           | _ -> assert false);
        `Assoc [ ("id", `String id); ("strings", `List (List.map snd strings)) ])
      cases
  in
  match Sys.getenv_opt "GILLIAN_UTF16_BRIDGE_MODELS" with
  | None -> ()
  | Some path -> Yojson.Safe.to_file path (`List evidence)

let tests =
  [
    ("all code units", `Quick, all_units);
    ("finite concatenations", `Quick, finite_sequences);
    ("canonical input domain", `Quick, input_domain);
    ("model syntax and width", `Quick, model_domain);
    ("arbitrary native sequences", `Quick, symbolic_laws);
    ("recovered solver models", `Quick, models);
  ]
