open Gillian.Gil_syntax
module Spec = Jsil_syntax.Spec
module Lower = Js2jsil_lib.JSIL2GIL

let parse ?(body = "ret := n; return") cases =
  let text = "spec count(n)\n" ^ cases ^ "\nproc count(n) { " ^ body ^ " };" in
  let file = Filename.temp_file "jsil-variant-" ".jsil" in
  let prog =
    Fun.protect
      ~finally:(fun () -> Sys.remove file)
      (fun () ->
        let out = open_out file in
        output_string out text;
        close_out out;
        Parsing.parse_jsil_eprog_from_file file)
  in
  Option.get (Option.get (Jsil_syntax.EProg.get_proc prog "count")).spec

let check_expr label expected actual =
  Alcotest.(check bool) label true (Option.equal Expr.equal expected actual)

let check_case (a : Spec.st) (b : Spec.st) =
  Alcotest.(check bool)
    "pre/post/flag/label/verification preserved" true
    (a.pre = b.pre && a.posts = b.posts && a.flag = b.flag && a.label = b.label
   && a.to_verify = b.to_verify);
  Alcotest.(check bool) "variant preserved" true (a.variant = b.variant)

let roundtrip flag () =
  let spec =
    parse ("<base> [[ (n == #n) ]] [[ (ret == #n) ]] variant(n) " ^ flag)
  in
  let original = List.hd spec.sspecs in
  Alcotest.(check bool)
    "parsed formal rank" true
    (original.variant = Some (Spec.Expression (Expr.PVar "n")));
  let printed = Format.asprintf "%a" Spec.pp_sspec original in
  let recovered = List.hd (parse printed).sspecs in
  check_case original recovered;
  let gil = Lower.jsil2gil_sspec recovered in
  check_expr "rank reaches GIL" (Some (Expr.PVar "n")) gil.ss_variant;
  Alcotest.(check bool)
    "return flag reaches GIL" true
    (original.flag = gil.ss_flag)

let legacy () =
  let original =
    List.hd (parse "[[ (n == #n) ]] [[ (ret == #n) ]] normal").sspecs
  in
  Alcotest.(check bool)
    "missing rank stays absent" true (original.variant = None);
  check_expr "legacy lowering stays absent" None
    (Lower.jsil2gil_sspec original).ss_variant;
  let constructed =
    Spec.s_init original.pre original.posts original.flag true
  in
  check_case original constructed;
  let printed = Format.asprintf "%a" Spec.pp_sspec original in
  check_case original (List.hd (parse printed).sspecs)

let multiple_cases () =
  let spec =
    parse
      "<base> [[ (n == 0) ]] [[ (ret == 0) ]] variant(n) normal;\n\
       <step> [[ (n == #n) ]] [[ (ret == #n) ]] variant(n - 1) error"
  in
  let gil = Lower.jsil2gil_spec spec in
  Alcotest.(check int) "both cases retained" 2 (List.length gil.spec_sspecs);
  List.iter2
    (fun (original : Spec.st) (lowered : Gillian.Gil_syntax.Spec.st) ->
      check_expr "per-case rank lowered"
        (Option.map Lower.jsil2gil_procedure_variant original.variant)
        lowered.ss_variant;
      Alcotest.(check bool)
        "per-case label and flag retained" true
        (Option.map
           (fun (name, vars) -> (name, Spec.SS.elements vars))
           original.label
         = lowered.ss_label
        && original.flag = lowered.ss_flag);
      check_case original
        (List.hd (parse (Format.asprintf "%a" Spec.pp_sspec original)).sspecs))
    spec.sspecs gil.spec_sspecs;
  Alcotest.(check bool)
    "different ranks not collapsed" false
    (Option.equal Expr.equal (List.nth gil.spec_sspecs 0).ss_variant
       (List.nth gil.spec_sspecs 1).ss_variant)

let list_length () =
  let original =
    List.hd (parse "[[ emp ]] [[ emp ]] variant(l-len n) normal").sspecs
  in
  Alcotest.(check bool)
    "parsed JSIL list length" true
    (original.variant
    = Some (Spec.Expression (Expr.UnOp (LstLen, Expr.PVar "n"))));
  check_expr "length rank remains a JS number"
    (Some (Expr.UnOp (IntToNum, Expr.UnOp (LstLen, Expr.PVar "n"))))
    (Lower.jsil2gil_sspec original).ss_variant

let integer_list_length flag () =
  let original =
    List.hd (parse ("[[ emp ]] [[ emp ]] variant(l-len-int n) " ^ flag)).sspecs
  in
  Alcotest.(check bool)
    "distinct structural rank" true
    (original.variant = Some (Spec.ListLength "n"));
  let recovered =
    List.hd (parse (Format.asprintf "%a" Spec.pp_sspec original)).sspecs
  in
  check_case original recovered;
  check_expr "exact GIL integer length, no numeric conversion"
    (Some (Expr.UnOp (LstLen, Expr.PVar "n")))
    (Lower.jsil2gil_sspec recovered).ss_variant

let structural_rank_is_not_executable () =
  let rejects body suffix =
    let rejected =
      try
        ignore (parse ~body ("[[ emp ]] [[ emp ]] " ^ suffix));
        false
      with Failure _ -> true
    in
    Alcotest.(check bool)
      "invalid structural-rank position rejected" true rejected
  in
  rejects "ret := l-len-int n; return" "normal";
  List.iter
    (rejects "ret := n; return")
    [
      "variant(l-len-int) normal";
      "variant(l-len-int #n) normal";
      "variant(l-len-int (n)) normal";
      "variant(l-len-int n + 1) normal";
    ];
  (* Ordinary expressions retain binary64 length, including the explicit cast. *)
  let length = Expr.UnOp (LstLen, Expr.PVar "n") in
  let numeric = Expr.UnOp (IntToNum, length) in
  check_expr "ordinary numeric length unchanged" (Some numeric)
    (Some (Lower.jsil2gil_expr length));
  check_expr "ordinary cast still crosses the numeric boundary"
    (Some (Expr.UnOp (NumToInt, numeric)))
    (Some (Lower.jsil2gil_expr (Expr.UnOp (NumToInt, length))))

let malformed () =
  List.iter
    (fun suffix ->
      let rejected =
        try
          ignore (parse ("[[ emp ]] [[ emp ]] " ^ suffix));
          false
        with Failure _ -> true
      in
      Alcotest.(check bool) "malformed rank rejected" true rejected)
    [ "variant() normal"; "variant(n normal"; "variant(n) variant(n) normal" ]

let () =
  Alcotest.run "JSIL procedure variants"
    [
      ( "frontend",
        [
          Alcotest.test_case "normal roundtrip" `Quick (roundtrip "normal");
          Alcotest.test_case "error roundtrip" `Quick (roundtrip "error");
          Alcotest.test_case "legacy defaults" `Quick legacy;
          Alcotest.test_case "per-case variants" `Quick multiple_cases;
          Alcotest.test_case "numeric list-length lowering" `Quick list_length;
          Alcotest.test_case "malformed ranks" `Quick malformed;
          Alcotest.test_case "integer length normal roundtrip" `Quick
            (integer_list_length "normal");
          Alcotest.test_case "integer length error roundtrip" `Quick
            (integer_list_length "error");
          Alcotest.test_case "integer rank syntax boundary" `Quick
            structural_rank_is_not_executable;
        ] );
    ]
