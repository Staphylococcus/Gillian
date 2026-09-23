let check = Alcotest.(check (list int))
let decode = Semantics.Utf16.code_units

let code_units () =
  (* Include every lone surrogate as well as every ordinary BMP code unit. *)
  for unit = 0 to 0xffff do
    let buffer = Buffer.create 3 in
    Wtf8.add_wtf_8 buffer unit;
    check "one code unit" [ unit ] (decode (Buffer.contents buffer))
  done;
  check "empty" [] (decode "");
  check "mixed UTF-8 and surrogate pair"
    [ 65; 233; 0xd83d; 0xde00; 0 ]
    (decode "A\xc3\xa9\xf0\x9f\x98\x80\x00");
  check "escaped surrogate pair representation" [ 0xd83d; 0xde00 ]
    (decode "\xed\xa0\xbd\xed\xb8\x80");
  check "lowest astral code point" [ 0xd800; 0xdc00 ]
    (decode "\xf0\x90\x80\x80");
  check "highest Unicode code point" [ 0xdbff; 0xdfff ]
    (decode "\xf4\x8f\xbf\xbf")

let malformed () =
  List.iter
    (fun string ->
      let rejected =
        try
          ignore (decode string);
          false
        with Gillian.Utils.Exceptions.Unsupported _ -> true
      in
      Alcotest.(check bool) "invalid encoding is unsupported" true rejected)
    [
      "\x80";
      "\xc0\x80";
      "\xc2";
      "\xc2A";
      "\xe0\x80\x80";
      "\xf0\x80\x80\x80";
      "\xf4\x90\x80\x80";
      "\xff";
    ]

let canonical () =
  let module U = Semantics.Utf16 in
  let check = Alcotest.(check string) in
  check "literal and escaped pair"
    (U.canonical "\xf0\x9f\x98\x80")
    (U.of_code_units [ 0xd83d; 0xde00 ]);
  check "concatenation"
    (U.canonical "\xf0\x9f\x98\x80")
    (U.of_code_units [ 0xd83d ] ^ U.of_code_units [ 0xde00 ]);
  check "source text" "\xf0\x9f\x98\x80"
    (U.source_text (U.of_code_units [ 0xd83d; 0xde00 ]));
  for unit = 0 to 0xffff do
    Alcotest.(check (list int))
      "encode roundtrip" [ unit ]
      (U.code_units (U.of_code_units [ unit ]))
  done

let lowering () =
  let open Gillian.Gil_syntax in
  let module M = Js2jsil_lib.JSIL2GIL in
  let typed = Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "callee") in
  Alcotest.(check bool)
    "JS data and procedure identifiers keep distinct kinds" true
    (M.jsil2gil_expr (Expr.string "callee") = Expr.Lit typed
    && M.jsil2gil_target (Expr.string "callee") = Expr.string "callee");
  Alcotest.(check bool)
    "nested literal and type annotations use the JS domain" true
    (M.jsil2gil_expr
       (Expr.Lit (Literal.LList [ String "callee"; Type StringType ]))
    = Expr.Lit (Literal.LList [ typed; Type Utf16Type ]));
  Alcotest.(check bool)
    "symbolic string admission changes its type" true
    (M.jsil2gil_lcmd
       (Jsil_syntax.LCmd.AssumeType (Expr.PVar "value", Type.StringType))
    = LCmd.AssumeType (Expr.PVar "value", Type.Utf16Type));
  Alcotest.(check bool)
    "quantified JS strings use the same type as their bodies" true
    (M.jsil2gil_expr
       (Expr.ForAll
          ( [ ("#s", Some Type.StringType) ],
            Expr.BinOp
              ( Expr.UnOp (TypeOf, Expr.LVar "#s"),
                Equal,
                Expr.Lit (Type StringType) ) ))
    = Expr.ForAll
        ( [ ("#s", Some Type.Utf16Type) ],
          Expr.BinOp
            ( Expr.UnOp (TypeOf, Expr.LVar "#s"),
              Equal,
              Expr.Lit (Type Utf16Type) ) ))

let () =
  Alcotest.run "JavaScript UTF-16"
    [
      ( "decode",
        [
          ("code units", `Quick, code_units);
          ("malformed", `Quick, malformed);
          ("canonical", `Quick, canonical);
          ("lowering boundaries", `Quick, lowering);
        ] );
    ]
