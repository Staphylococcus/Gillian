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

let tests = [ ("GIL literal escaping", `Quick, literal_roundtrip) ]
