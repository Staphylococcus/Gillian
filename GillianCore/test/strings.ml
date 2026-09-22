open Gillian.Gil_syntax
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let literal_roundtrip () =
  List.iter
    (fun string ->
      let literal = Literal.String string in
      let printed = Fmt.str "%a" Literal.pp literal in
      match Parser.parse_literal (Lexing.from_string printed) with
      | Ok parsed ->
          Alcotest.(check bool)
            "GIL string value survives printing and parsing" true
            (Literal.equal literal parsed)
      | Error _ -> Alcotest.fail "Printed GIL string could not be parsed")
    [
      "";
      "quote: \"";
      "slash: \\";
      "\\\"";
      "\n\r\t\b\012\x00";
      "\xc3\xa9\xf0\x9f\x98\x80";
      "\xed\xa0\x80";
    ]

module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver

let a = Expr.LVar "#bytes_a"
let b = Expr.LVar "#bytes_b"
let c = Expr.LVar "#bytes_c"
let literal s = Expr.Lit (Literal.String s)
let equal a b = Expr.BinOp (a, Equal, b)
let concat a b = Expr.BinOp (a, StrCat, b)
let not_ p = Expr.UnOp (Not, p)

let gamma () =
  let gamma = Gamma.init () in
  List.iter
    (fun name -> Gamma.update gamma name Type.StringType)
    [ "#bytes_a"; "#bytes_b"; "#bytes_c" ];
  gamma

let check label expected formulas =
  let gamma = gamma () in
  Alcotest.(check bool)
    (label ^ " (SMT)") expected
    (Smt.is_sat (Expr.Set.of_list formulas) (Gamma.as_hashtbl gamma));
  Alcotest.(check bool)
    (label ^ " (simplifier + SMT)")
    expected
    (Solver.check_satisfiability formulas gamma)

let byte_contents () =
  let all = String.init 256 Char.chr in
  check "every byte survives concatenation" false
    [
      equal a (literal (String.sub all 0 128));
      equal b (literal (String.sub all 128 128));
      not_ (equal (concat a b) (literal all));
    ];
  check "NUL is not empty" true [ not_ (equal (literal "\x00") (literal "")) ];
  check "bytes are not silently normalized" true
    [
      not_
        (equal
           (literal "\xed\xa0\xbd\xed\xb8\x80")
           (literal "\xf0\x9f\x98\x80"));
    ];
  check "surrogate units concatenate as bytes" false
    [
      equal a (literal "\xed\xa0\xbd");
      equal b (literal "\xed\xb8\x80");
      not_ (equal (concat a b) (literal "\xed\xa0\xbd\xed\xb8\x80"));
    ]

let symbolic_concat () =
  check "associativity" false
    [ not_ (equal (concat a (concat b c)) (concat (concat a b) c)) ];
  check "left cancellation" false
    [ equal (concat a b) (concat a c); not_ (equal b c) ];
  check "noncommutative counterexample exists" true
    [ not_ (equal (concat a b) (concat b a)) ];
  let gamma = Hashtbl.create 0 in
  Alcotest.(check bool)
    "untyped byte sequence wrapping" false
    (Smt.is_sat
       (Expr.Set.of_list
          [
            equal a (literal "left");
            equal b (literal "right");
            not_ (equal (concat a b) (literal "leftright"));
          ])
       gamma)

let model_roundtrip () =
  let gamma = gamma () |> Gamma.as_hashtbl in
  let lift formulas =
    match Smt.check_sat (Expr.Set.of_list formulas) gamma with
    | None -> Alcotest.fail "missing string counterexample"
    | Some model -> (
        let lifted = ref None in
        Smt.lift_model model gamma
          (fun _ value -> lifted := Some value)
          (Expr.Set.singleton a);
        match !lifted with
        | Some (Expr.Lit (Literal.String bytes)) -> bytes
        | _ -> Alcotest.fail "model did not lift byte string")
  in
  let all = String.init 256 Char.chr in
  List.iter
    (fun bytes ->
      Alcotest.(check string)
        "literal model byte preservation" bytes
        (lift [ equal a (literal bytes) ]))
    [ ""; all; "\xed\xa0\x80" ];
  let bytes = lift [ not_ (equal a (literal "")) ] in
  Alcotest.(check bool)
    "fresh symbolic model replays" true
    (String.length bytes > 0)

let byte_values () =
  let bytes e = Expr.UnOp (StrToBytes, e) in
  let all = String.init 256 Char.chr in
  let expected =
    Expr.EList (List.init 256 (fun value -> Expr.num (float_of_int value)))
  in
  check "byte values preserve all 256 values" false
    [ equal a (literal all); not_ (equal (bytes a) expected) ];
  check "mapping preserves concatenation" false
    [
      not_
        (equal (bytes (concat a b)) (Expr.NOp (LstCat, [ bytes a; bytes b ])));
    ];
  let first = Expr.BinOp (bytes a, LstNth, Expr.int 0) in
  check "byte values remain in range" false
    [
      Expr.BinOp (Expr.int 0, ILessThan, Expr.UnOp (LstLen, bytes a));
      not_ (Expr.BinOp (first, FLessThanEqual, Expr.num 255.));
    ]

let tests =
  [
    ("GIL literal escaping", `Quick, literal_roundtrip);
    ("byte-value sequences", `Quick, byte_values);
    ("native byte contents", `Quick, byte_contents);
    ("symbolic concatenation", `Quick, symbolic_concat);
    ("byte counterexample models", `Quick, model_roundtrip);
  ]
