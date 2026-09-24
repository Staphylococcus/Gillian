open Gillian.Gil_syntax
module Codec = Gillian.Utils.Utf16
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Reduction = Gillian.Logic.Reduction
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let literal units =
  Literal.Utf16String (Codec.of_canonical (Codec.of_code_units units))

let value units = Expr.Lit (literal units)
let bin op a b = Expr.BinOp (a, op, b)
let eq = bin Equal
let cat = bin Utf16Cat
let length e = Expr.UnOp (Utf16Len, e)
let not_ e = Expr.UnOp (Not, e)
let a = Expr.LVar "#utf16_a"
let b = Expr.LVar "#utf16_b"
let c = Expr.LVar "#utf16_c"

let gamma () =
  let gamma = Gamma.init () in
  List.iter
    (fun name -> Gamma.update gamma name Type.Utf16Type)
    [ "#utf16_a"; "#utf16_b"; "#utf16_c" ];
  gamma

let check ?(types = gamma) label expected constraints =
  Alcotest.(check bool)
    (label ^ " (SMT)") expected
    (Smt.is_sat (Expr.Set.of_list constraints) (Gamma.as_hashtbl (types ())));
  Alcotest.(check bool)
    (label ^ " (reduction + SMT)")
    expected
    (Solver.check_satisfiability constraints (types ()))

let values =
  [
    [];
    [ 0 ];
    [ 65; 0xe9; 0x7ff; 0x800; 0xffff ];
    [ 0xd83d; 0xde00 ];
    [ 0xd800 ];
    [ 0xdfff ];
    [ 0; 0xd800; 0x61; 0xdc00; 0xffff ];
  ]

let literal_domain () =
  Alcotest.(check bool)
    "the explicit UTF-16 literal introducer normalizes scalar UTF-8" true
    (match
       Parser.parse_literal (Lexing.from_string "u16\"\xf0\x9f\x98\x80\"")
     with
    | Ok parsed -> Literal.equal parsed (literal [ 0xd83d; 0xde00 ])
    | Error _ -> false);
  List.iter
    (fun units ->
      let lit = literal units in
      let printed = Fmt.str "%a" Literal.pp lit in
      let parsed = Parser.parse_literal (Lexing.from_string printed) in
      Alcotest.(check bool)
        "typed literal survives GIL printing/parsing" true
        (match parsed with
        | Ok parsed -> Literal.equal lit parsed
        | _ -> false);
      Alcotest.(check bool)
        "typed literal survives JSON transport" true
        (match Literal.of_yojson (Literal.to_yojson lit) with
        | Ok parsed -> Literal.equal lit parsed
        | Error _ -> false))
    values;
  List.iter
    (fun bytes ->
      let rejected =
        try
          ignore (Codec.of_canonical bytes);
          false
        with Gillian.Utils.Exceptions.Unsupported _ -> true
      in
      Alcotest.(check bool)
        "invalid literal construction is rejected" true rejected;
      Alcotest.(check bool)
        "JSON cannot bypass the literal domain" true
        (Result.is_error
           (Literal.of_yojson (`List [ `String "Utf16String"; `String bytes ]))))
    [ "\x80"; "\xc0\x80"; "\xc2A"; "\xf0\x9f\x98\x80" ]

let concrete_agreement () =
  let store = Engine.CExprEval.CStore.init [] in
  let check_term term expected =
    Alcotest.(check bool)
      "concrete operation preserves code units" true
      (Literal.equal expected (Engine.CExprEval.evaluate_expr store term));
    Alcotest.(check bool)
      "ground reduction agrees with concrete evaluation" true
      (Expr.equal (Expr.Lit expected) (Reduction.reduce_lexpr term));
    check "direct SMT agrees with concrete evaluation" false
      [ not_ (eq term (Expr.Lit expected)) ]
  in
  List.iter
    (fun left ->
      check_term
        (length (value left))
        (Literal.Int (Z.of_int (List.length left)));
      List.iter
        (fun right ->
          check_term (cat (value left) (value right)) (literal (left @ right));
          check_term
            (eq (value left) (value right))
            (Literal.Bool (left = right)))
        values)
    values

let arbitrary_values () =
  check "length is nonnegative" false [ bin ILessThan (length a) (Expr.int 0) ];
  check "concatenation length" false
    [ not_ (eq (length (cat a b)) (bin IPlus (length a) (length b))) ];
  check "concatenation associativity" false
    [ not_ (eq (cat a (cat b c)) (cat (cat a b) c)) ];
  check "prefix cancellation" false [ eq (cat a b) (cat a c); not_ (eq b c) ];
  check "order is observable" true [ not_ (eq (cat a b) (cat b a)) ];
  check "surrogate pair counts twice" false
    [ eq a (value [ 0xd83d; 0xde00 ]); not_ (eq (length a) (Expr.int 2)) ];
  check "length is not byte length" true
    [ eq a (value [ 0xd83d; 0xde00 ]); not_ (eq (length a) (Expr.int 6)) ];
  check "length is not code-point length" true
    [ eq a (value [ 0xd83d; 0xde00 ]); not_ (eq (length a) (Expr.int 1)) ]

let js_length_conversion () =
  let store = Engine.CExprEval.CStore.init [] in
  let check_term term expected =
    let literal = Literal.Num expected in
    Alcotest.(check bool)
      "JS length conversion agrees with the expected Number" true
      (Literal.same_value literal (Engine.CExprEval.evaluate_expr store term));
    Alcotest.(check bool)
      "reduction retains binary64 rounding" true
      (Expr.equal (Expr.Lit literal) (Reduction.reduce_lexpr term));
    check "SMT conversion agrees without concrete reduction" false
      [ not_ (bin ValueEqual term (Expr.Lit literal)) ]
  in
  List.iter
    (fun units ->
      check_term
        (Expr.UnOp (IntToNum, length (value units)))
        (float_of_int (List.length units)))
    values;
  (* The JS String domain ends at 2^53-1; generic GIL integers do not. Keep
     round-to-nearest/ties-to-even outside that language domain. These are
     boundary controls, not an enumeration proof of integer exactness. *)
  List.iter
    (fun (integer, expected) ->
      check_term
        (Expr.UnOp (IntToNum, Expr.Lit (Int (Z.of_string integer))))
        expected)
    [
      ("0", 0.);
      ("-1", -1.);
      ("1", 1.);
      ("65535", 65535.);
      ("65536", 65536.);
      (Z.to_string (Z.shift_left Z.one 1024), infinity);
      (Z.to_string (Z.neg (Z.shift_left Z.one 1024)), neg_infinity);
      ("9007199254740991", 9007199254740991.);
      ("9007199254740992", 9007199254740992.);
      ("9007199254740993", 9007199254740992.);
      ("9007199254740995", 9007199254740996.);
    ]

(* Constrain mathematical lengths, without allocating enormous strings or
   asking the model decoder to materialize them. Direct SMT exercises the
   length-specific encoding; literal conversion checks the concrete and
   reduction paths, including the fallback's rounding and overflow. *)
let length_conversion_boundaries () =
  let store = Engine.CExprEval.CStore.init [] in
  let overflow_midpoint =
    Z.sub (Z.shift_left Z.one 1024) (Z.shift_left Z.one 970)
  in
  List.iter
    (fun (integer, expected) ->
      let integer = Expr.Lit (Literal.Int integer) in
      let expected = Expr.Lit (Literal.Num expected) in
      let literal_conversion = Expr.UnOp (IntToNum, integer) in
      Alcotest.(check bool)
        "concrete boundary conversion" true
        (Expr.equal expected
           (Expr.Lit (Engine.CExprEval.evaluate_expr store literal_conversion)));
      Alcotest.(check bool)
        "reduced boundary conversion" true
        (Expr.equal expected (Reduction.reduce_lexpr literal_conversion));
      check "symbolic length conversion boundary" false
        [
          eq (length a) integer;
          not_ (bin ValueEqual (Expr.UnOp (IntToNum, length a)) expected);
        ];
      let is_integral = Expr.UnOp (IsInt, Expr.UnOp (IntToNum, length a)) in
      let concrete_integral =
        Engine.CExprEval.evaluate_expr store
          (Expr.UnOp (IsInt, literal_conversion))
      in
      check "composite integrality agrees with concrete conversion" false
        [
          eq (length a) integer;
          not_ (eq is_integral (Expr.Lit concrete_integral));
        ];
      let bound = Expr.num 9007199254740991. in
      let comparison =
        bin FLessThanEqual (Expr.UnOp (IntToNum, length a)) bound
      in
      let concrete_bound =
        Engine.CExprEval.evaluate_expr store
          (bin FLessThanEqual literal_conversion bound)
      in
      check "composite bound agrees with original boundary conversion" false
        [
          eq (length a) integer; not_ (eq comparison (Expr.Lit concrete_bound));
        ])
    (List.map
       (fun (n, f) -> (Z.of_string n, f))
       [
         ("0", 0.);
         ("1", 1.);
         ("65535", 65535.);
         ("65536", 65536.);
         ("9007199254740991", 9007199254740991.);
         ("9007199254740992", 9007199254740992.);
         ("9007199254740993", 9007199254740992.);
         ("9007199254740995", 9007199254740996.);
       ]
    @ [
        (Z.pred overflow_midpoint, max_float);
        (overflow_midpoint, infinity);
        (Z.succ overflow_midpoint, infinity);
        (Z.shift_left Z.one 1024, infinity);
      ])

let language_length_integrality () =
  let len = length a in
  let number = Expr.UnOp (IntToNum, len) in
  let integral = Expr.UnOp (IsInt, number) in
  let language_max = Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))) in
  (* Universal over the JS String domain, including the full 53-bit range.
     Neither the native query nor the reducer may assume this conclusion. *)
  check "language-valid length converts to a finite integral Number" false
    [ bin ILessThanEqual len language_max; not_ integral ];
  check "language-valid integrality has a satisfiable witness" true
    [ bin ILessThanEqual len language_max; integral ];
  (* Generic GIL lengths remain unbounded. Finite rounded lengths are still
     integral, but overflow must not be certified as integral. *)
  check "rounded generic length stays integral" false
    [ eq len (Expr.Lit (Int (Z.succ (Z.shift_left Z.one 53)))); not_ integral ];
  check "overflowing generic length is not integral" false
    [ eq len (Expr.Lit (Int (Z.shift_left Z.one 1024))); integral ];
  check "integrality does not imply an empty string" true
    [ eq a (value [ 65 ]); integral; not_ (eq len (Expr.int 0)) ]

let length_nonnegative () =
  let len = length a in
  let number = Expr.UnOp (IntToNum, len) in
  List.iter
    (fun zero ->
      let nonnegative = bin FLessThanEqual (Expr.num zero) number in
      check "all converted lengths are nonnegative" false [ not_ nonnegative ];
      check "nonnegative length has an empty witness" true
        [ eq a (value []); nonnegative ];
      check "positive overflow remains nonnegative" false
        [ eq len (Expr.Lit (Int (Z.shift_left Z.one 1024))); not_ nonnegative ])
    [ 0.; -0. ];
  check "one is not a lower bound on an empty string" false
    [ eq a (value []); bin FLessThanEqual (Expr.num 1.) number ];
  (* The rule must not affect generic conversions or arbitrary Numbers. *)
  List.iter
    (fun integer ->
      check "negative integer conversion is not nonnegative" false
        [
          bin FLessThanEqual (Expr.num 0.)
            (Expr.UnOp (IntToNum, Expr.Lit (Int integer)));
        ])
    [ Z.minus_one; Z.neg (Z.shift_left Z.one 1024) ];
  List.iter
    (fun number ->
      check "negative and NaN Numbers are not nonnegative" false
        [ bin FLessThanEqual (Expr.num 0.) (Expr.num number) ])
    [ -1.; neg_infinity; nan ]

let language_length_bound () =
  let len = length a in
  let number = Expr.UnOp (IntToNum, len) in
  let maximum = Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))) in
  let bound = bin FLessThanEqual number (Expr.num 9007199254740991.) in
  check "language length has the numeric upper bound" false
    [ bin ILessThanEqual len maximum; not_ bound ];
  check "numeric bound cannot admit a larger mathematical length" false
    [ bin ILessThan maximum len; bound ];
  check "numeric bound admits empty strings" true [ eq a (value []); bound ];
  check "numeric bound does not imply empty strings" true
    [ eq a (value [ 65 ]); bound; not_ (eq len (Expr.int 0)) ];
  (* Neither other thresholds nor unrelated Number operands use this rule. *)
  check "nonempty strings do not satisfy a zero upper bound" false
    [ eq a (value [ 65 ]); bin FLessThanEqual number (Expr.num 0.) ];
  check "the next representable cutoff still admits its rounding tie" false
    [
      eq len (Expr.Lit (Int (Z.succ (Z.shift_left Z.one 53))));
      not_ (bin FLessThanEqual number (Expr.num 9007199254740992.));
    ];
  List.iter
    (fun n ->
      check "arbitrary large/NaN Numbers still fail the language bound" false
        [ bin FLessThanEqual (Expr.num n) (Expr.num 9007199254740991.) ])
    [ 9007199254740992.; infinity; nan ]

let replay_length_model gamma constraints model =
  let index = Expr.LVar "#length_index" in
  let lifted = Hashtbl.create 2 in
  Smt.lift_model model gamma (Hashtbl.add lifted)
    (Expr.Set.of_list [ a; index ]);
  let get name =
    match Hashtbl.find_opt lifted name with
    | Some (Expr.Lit value) -> value
    | _ -> Alcotest.fail "Missing length/index model value"
  in
  let units =
    match get "#utf16_a" with
    | Utf16String value -> Codec.code_units (Codec.to_canonical value)
    | _ -> Alcotest.fail "Lost string model type"
  in
  let number =
    match get "#length_index" with
    | Num value -> value
    | _ -> Alcotest.fail "Lost numeric model type"
  in
  let store =
    Engine.CExprEval.CStore.init
      [ ("#utf16_a", get "#utf16_a"); ("#length_index", Num number) ]
  in
  let visitor =
    object
      inherit [_] Visitors.endo
      method! visit_LVar () _ name = Expr.PVar name
    end
  in
  List.iter
    (fun expr ->
      match
        Engine.CExprEval.evaluate_expr store (visitor#visit_expr () expr)
      with
      | Bool true -> ()
      | _ -> Alcotest.fail "Length model failed concrete replay")
    constraints;
  [
    ("units", `List (List.map (fun unit -> `Int unit) units));
    ("indexBits", `String (Printf.sprintf "%016Lx" (Int64.bits_of_float number)));
  ]

let length_branch_models () =
  let index = Expr.LVar "#length_index" in
  let gamma = gamma () in
  Gamma.update gamma "#length_index" NumberType;
  let gamma = Gamma.as_hashtbl gamma in
  let pos = Expr.UnOp (ToIntOp, index) in
  let nonnegative = not_ (bin FLessThan pos (Expr.num 0.)) in
  let outside = bin FLessThanEqual (Expr.UnOp (IntToNum, length a)) pos in
  let models =
    List.map
      (fun (id, guard) ->
        let constraints = [ nonnegative; guard ] in
        let model =
          match Smt.exec_sat (Expr.Set.of_list constraints) gamma with
          | Some model -> model
          | None -> Alcotest.fail ("Lost feasible length branch: " ^ id)
        in
        `Assoc
          (("id", `String id) :: replay_length_model gamma constraints model))
      [ ("outside", outside); ("inside", not_ outside) ]
  in
  match Sys.getenv_opt "GILLIAN_UTF16_COMPARISON_MODELS" with
  | None -> ()
  | Some path -> Yojson.Safe.to_file path (`List models)

(* Replay the actual reduced terms, including exceptional Numbers. The
   arbitrary-input JS controls separately prove the composed runtime path. *)
let comparison_reduction () =
  let gamma = gamma () in
  Gamma.update gamma "#length_index" NumberType;
  let index = Expr.LVar "#length_index" in
  let pos = Expr.UnOp (ToIntOp, index) in
  let len = Expr.UnOp (IntToNum, length a) in
  let terms =
    [
      eq len len;
      eq len (Expr.num 0.);
      eq (Expr.num (-0.)) len;
      bin FLessThan len len;
      bin FLessThanEqual len len;
      eq pos pos;
      bin FLessThan pos pos;
      bin FLessThanEqual pos pos;
      bin FLessThan pos len;
      eq index index;
      bin FLessThan index len;
    ]
  in
  let terms =
    List.map (fun term -> (term, Reduction.reduce_lexpr ~gamma term)) terms
  in
  let visitor =
    object
      inherit [_] Visitors.endo
      method! visit_LVar () _ name = Expr.PVar name
    end
  in
  List.iter
    (fun units ->
      List.iter
        (fun n ->
          let store =
            Engine.CExprEval.CStore.init
              [ ("#utf16_a", literal units); ("#length_index", Num n) ]
          in
          let eval e =
            Engine.CExprEval.evaluate_expr store (visitor#visit_expr () e)
          in
          List.iter
            (fun (original, reduced) ->
              Alcotest.(check bool)
                "comparison reduction preserves native result" true
                (Literal.equal (eval original) (eval reduced)))
            terms)
        [
          nan;
          infinity;
          neg_infinity;
          0.;
          -0.;
          -1.;
          -0.5;
          0.5;
          1.;
          1.5;
          65536.;
          9007199254740992.;
          Float.max_float;
        ])
    values

let length_comparison_numbers () =
  List.iter
    (fun units ->
      List.iter
        (fun number ->
          let condition =
            bin FLessThanEqual
              (Expr.UnOp (IntToNum, length a))
              (Expr.num number)
          in
          let expected = float_of_int (List.length units) <= number in
          let actual = if expected then condition else not_ condition in
          check "length comparison retains Number outcome" true
            [ eq a (value units); actual ];
          check "length comparison rejects opposite outcome" false
            [ eq a (value units); not_ actual ])
        [
          nan;
          infinity;
          neg_infinity;
          0.;
          -0.;
          -1.;
          -0.5;
          0.5;
          1.;
          1.5;
          65536.;
          9007199254740992.;
          Float.max_float;
        ])
    [ []; [ 65 ]; [ 0xd83d; 0xde00 ] ]

let composition_models () =
  let gamma = gamma () in
  Gamma.update gamma "#length_index" NumberType;
  let index = Expr.LVar "#length_index" in
  let pos = Expr.UnOp (ToIntOp, index) in
  let negative = bin FLessThan pos (Expr.num 0.) in
  let outside = bin FLessThanEqual (Expr.UnOp (IntToNum, length a)) pos in
  let models =
    List.map
      (fun (id, constraints) ->
        let model =
          match
            Smt.exec_sat (Expr.Set.of_list constraints) (Gamma.as_hashtbl gamma)
          with
          | Some model -> model
          | None -> Alcotest.fail ("Lost feasible composition outcome: " ^ id)
        in
        `Assoc
          (("id", `String id)
          :: replay_length_model (Gamma.as_hashtbl gamma) constraints model))
      [
        ("negative", [ negative; eq a a ]);
        ("outside", [ not_ negative; outside ]);
        ("inside", [ not_ negative; not_ outside ]);
      ]
  in
  match Sys.getenv_opt "GILLIAN_UTF16_COMPOSITION_MODELS" with
  | None -> ()
  | Some path -> Yojson.Safe.to_file path (`List models)

(* Use the standard false-first heuristic to expose a known invalid-model
   case on Z3 4.13.3. Only this test changes the search policy; production keeps
   the default. The mixed-theory query is feasible, but the returned empty
   string witness violates its inside guard and must never escape the solver. *)
let length_model_validation () =
  let index = Expr.LVar "#length_index" in
  let gamma = gamma () in
  Gamma.update gamma "#length_index" NumberType;
  let gamma = Gamma.as_hashtbl gamma in
  let pos = Expr.UnOp (ToIntOp, index) in
  let nonnegative = not_ (bin FLessThan pos (Expr.num 0.)) in
  (* Exercise the unchanged generic IntToNum encoding: the length-specific
     fast path can avoid this solver defect. Direct exec_sat does not reduce
     the syntactic +0 before choosing the conversion encoding. *)
  let general_length = bin IPlus (length a) (Expr.int 0) in
  let outside = bin FLessThanEqual (Expr.UnOp (IntToNum, general_length)) pos in
  let run () =
    let model =
      match
        Smt.exec_sat ~phase_selection:0
          (Expr.Set.of_list [ nonnegative; outside ])
          gamma
      with
      | Some model -> model
      | None -> Alcotest.fail "Lost the feasible outside branch"
    in
    let witness = replay_length_model gamma [ nonnegative; outside ] model in
    let rejected =
      try
        ignore
          (Smt.exec_sat ~phase_selection:0
             (Expr.Set.of_list [ nonnegative; not_ outside ])
             gamma);
        false
      with
      | Gillian.Utils.Gillian_result.Exc.Gillian_internal_error { msg; _ } -> (
        let contains = Str.regexp_string "an invalid model was generated" in
        try
          ignore (Str.search_forward contains msg 0);
          true
        with Not_found -> false)
    in
    Alcotest.(check bool) "invalid inside model is rejected" true rejected;
    (* The heartbeat replaces the faulty solver before propagating failure. *)
    check "solver remains usable after rejected model" true
      [ eq a (value [ 65 ]) ];
    let evidence =
      `Assoc
        (("id", `String "outside")
        :: ("invalidInsideModelRejected", `Bool rejected)
        :: witness)
    in
    match Sys.getenv_opt "GILLIAN_UTF16_LENGTH_MODELS" with
    | None -> ()
    | Some path -> Yojson.Safe.to_file path evidence
  in
  run ()

let wrapped_values () =
  check ~types:Gamma.init "untyped values acquire the same unit view" false
    [
      eq a (value [ 0xd800 ]);
      eq b (value [ 0xdc00 ]);
      not_ (eq (length (cat a b)) (Expr.int 2));
    ];
  let wrapped e = Expr.EList [ e ] in
  check "wrapped identity preserves units" false
    [
      eq a (value [ 0xd800 ]);
      not_ (bin ValueEqual (wrapped a) (wrapped (value [ 0xd800 ])));
    ];
  check "raw bytes and typed units remain different values" false
    [ eq (value [ 0 ]) (Expr.Lit (String "\x00")) ];
  check ~types:Gamma.init "wrapped byte/unit equality stays distinct" false
    [ eq a (value [ 0 ]); eq a (Expr.Lit (String "\x00")) ];
  let types () =
    let gamma = Gamma.init () in
    Gamma.update gamma "#utf16_a" StringType;
    gamma
  in
  let typed = eq (Expr.UnOp (TypeOf, a)) (Expr.Lit (Type Utf16Type)) in
  check "UTF-16 type is represented" true [ typed ];
  check ~types "cache does not confuse the two string types" false [ typed ]

let models () =
  let cases =
    [
      ("empty", [ eq a (value []) ], [ a ]);
      ("lone-high", [ eq a (value [ 0xd800 ]) ], [ a ]);
      ("lone-low", [ eq a (value [ 0xdc00 ]) ], [ a ]);
      ("astral-pair", [ eq a (value [ 0xd83d; 0xde00 ]) ], [ a ]);
      ( "mixed",
        [ eq a (value [ 0; 65; 0xe9; 0xd83d; 0xde00; 0xd800; 0xffff ]) ],
        [ a ] );
      ("arbitrary-nonempty", [ not_ (eq a (value [])) ], [ a ]);
      ("concat-order", [ not_ (eq (cat a b) (cat b a)) ], [ a; b ]);
    ]
  in
  let evidence =
    List.map
      (fun (id, constraints, variables) ->
        let gamma = Gamma.as_hashtbl (gamma ()) in
        let model =
          match Smt.check_sat (Expr.Set.of_list constraints) gamma with
          | Some model -> model
          | None -> Alcotest.fail "Missing typed UTF-16 model"
        in
        let lifted = Hashtbl.create 2 in
        Smt.lift_model model gamma (Hashtbl.add lifted)
          (Expr.Set.of_list variables);
        let literals =
          List.map
            (function
              | Expr.LVar name -> (
                  match Hashtbl.find_opt lifted name with
                  | Some (Expr.Lit (Utf16String _ as literal)) -> (name, literal)
                  | _ -> Alcotest.fail "Model lost its UTF-16 type")
              | _ -> assert false)
            variables
        in
        let store = Engine.CExprEval.CStore.init literals in
        let replay expr =
          let visitor =
            object
              inherit [_] Visitors.endo
              method! visit_LVar () _ name = Expr.PVar name
            end
          in
          match
            Engine.CExprEval.evaluate_expr store (visitor#visit_expr () expr)
          with
          | Literal.Bool true -> ()
          | _ ->
              Alcotest.fail "Recovered model did not replay its GIL constraints"
        in
        List.iter replay constraints;
        let strings =
          List.map
            (fun (_, literal) ->
              match literal with
              | Literal.Utf16String value ->
                  `Assoc
                    [
                      ( "units",
                        `List
                          (List.map
                             (fun u -> `Int u)
                             (Codec.code_units (Codec.to_canonical value))) );
                    ]
              | _ -> assert false)
            literals
        in
        `Assoc [ ("id", `String id); ("strings", `List strings) ])
      cases
  in
  match Sys.getenv_opt "GILLIAN_UTF16_TYPED_MODELS" with
  | None -> ()
  | Some path -> Yojson.Safe.to_file path (`List evidence)

let numeric_producers () =
  let store = Engine.CExprEval.CStore.init [] in
  let eval = Engine.CExprEval.evaluate_expr store in
  let check_term ?(exact_smt = true) term expected =
    Alcotest.(check bool)
      "typed numeric conversion matches the byte implementation" true
      (Literal.same_value expected (eval term));
    Alcotest.(check bool)
      "ground reduction retains the exact conversion" true
      (match Reduction.reduce_lexpr term with
      | Expr.Lit actual -> Literal.same_value expected actual
      | _ -> false);
    (* As for bytes, symbolic formatting of finite nonzero numbers is an
       over-approximation; its literal output is fixed by concrete reduction. *)
    if exact_smt then
      check "typed numeric conversion SMT agrees" false
        [ not_ (bin ValueEqual term (Expr.Lit expected)) ]
    else
      check "formatter admits its concrete spelling" true
        [ bin ValueEqual term (Expr.Lit expected) ]
  in
  List.iter
    (fun number ->
      let bytes =
        match eval (Expr.UnOp (ToStringOp, Expr.num number)) with
        | Literal.String bytes -> bytes
        | _ -> assert false
      in
      check_term
        ~exact_smt:(number = 0. || not (Float.is_finite number))
        (Expr.UnOp (NumberToUtf16, Expr.num number))
        (Literal.Utf16String (Codec.of_canonical bytes)))
    [
      0.;
      -0.;
      nan;
      infinity;
      neg_infinity;
      1.;
      0.1;
      1e-7;
      1e21;
      5e-324;
      Float.max_float;
    ];
  List.iter
    (fun bytes ->
      let bytes = Codec.canonical bytes in
      let expected = eval (Expr.UnOp (ToNumberOp, Expr.string bytes)) in
      check_term
        (Expr.UnOp
           ( Utf16ToNumber,
             Expr.Lit (Literal.Utf16String (Codec.of_canonical bytes)) ))
        expected)
    [
      "";
      "0";
      "-0";
      "01";
      "  42 ";
      "0x10";
      "+Infinity";
      "NaN";
      "push";
      "\xed\xa0\x80";
      "\xef\xbb\xbf12";
    ];
  let number = Expr.LVar "#number" in
  let types () =
    let g = Gamma.init () in
    Gamma.update g "#number" NumberType;
    g
  in
  let formatted = Expr.UnOp (NumberToUtf16, number) in
  let parsed = Expr.UnOp (Utf16ToNumber, formatted) in
  check ~types "symbolic formatter/parser preserves non-NaN numeric equality"
    false
    [ eq number number; not_ (eq parsed number) ];
  check ~types "symbolic formatter/parser preserves NaN" false
    [ not_ (eq number number); eq parsed parsed ];
  let reduced = Reduction.reduce_lexpr ~gamma:(types ()) parsed in
  check ~types "roundtrip reduction canonicalizes signed zero" false
    [ not_ (bin ValueEqual reduced (bin FPlus number (Expr.num 0.))) ];
  check ~types "numeric keys cannot collide with ordinary property names" false
    [ eq formatted (value [ 112; 117; 115; 104 ]) ];
  check ~types "native set keys retain the parser fact" false
    [ bin SetMem formatted (Expr.ESet [ value [ 112; 117; 115; 104 ] ]) ]

let concrete_legacy_operations () =
  let store = Engine.CExprEval.CStore.init [] in
  let eval = Engine.CExprEval.evaluate_expr store in
  Alcotest.(check bool)
    "legacy JSIL ordering compares code units" true
    (Literal.equal
       (eval (bin Utf16Less (value [ 0xd83d; 0xde00 ]) (value [ 0xe000 ])))
       (Literal.Bool true));
  Alcotest.(check bool)
    "legacy JSIL indexing returns a lone code unit" true
    (Literal.equal
       (eval (bin Utf16Nth (value [ 0xd83d; 0xde00 ]) (Expr.num 1.)))
       (literal [ 0xde00 ]))

let expression_transport () =
  List.iter
    (fun units ->
      let s = value units in
      List.iter
        (fun expr ->
          Alcotest.(check bool)
            "typed expression survives GIL export and reimport" true
            (match
               Parser.parse_expression
                 (Lexing.from_string (Fmt.str "%a" Expr.pp expr))
             with
            | Ok parsed -> Expr.equal expr parsed
            | Error _ -> false))
        [
          bin Utf16Nth s (Expr.num 0.);
          bin Utf16CodeUnit s (Expr.num 0.);
          bin Utf16Less s a;
          cat s a;
          length s;
          Expr.UnOp (Utf16ToNumber, s);
          Expr.UnOp (NumberToUtf16, Expr.num 1.);
        ])
    values

let with_total f =
  let old = !Gillian.Utils.Config.Verification.total in
  Gillian.Utils.Config.Verification.total := true;
  Fun.protect
    ~finally:(fun () -> Gillian.Utils.Config.Verification.total := old)
    f

let checked_index () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun units ->
      List.iteri
        (fun i unit ->
          let term = bin Utf16Nth (value units) (Expr.num (float_of_int i)) in
          Alcotest.(check bool)
            "concrete indexed unit" true
            (Literal.equal (literal [ unit ])
               (Engine.CExprEval.evaluate_expr store term));
          with_total (fun () ->
              check "SMT indexed unit" false [ not_ (eq term (value [ unit ])) ]))
        units;
      List.iter
        (fun index ->
          let rejected =
            try
              ignore
                (Engine.CExprEval.evaluate_expr store
                   (bin Utf16Nth (value units) (Expr.num index)));
              false
            with Engine.CExprEval.EvaluationError _ -> true
          in
          Alcotest.(check bool) "invalid concrete index rejected" true rejected)
        [
          nan;
          infinity;
          neg_infinity;
          -1.;
          0.5;
          float_of_int (List.length units);
          Float.max_float;
        ])
    values;
  with_total (fun () ->
      let types () =
        let g = gamma () in
        Gamma.update g "#length_index" NumberType;
        g
      in
      let index = Expr.LVar "#length_index" in
      let pos = Expr.UnOp (ToIntOp, index) in
      let size = length a in
      let offset = Expr.UnOp (NumToInt, pos) in
      let inside =
        [
          not_ (bin FLessThan pos (Expr.num 0.));
          not_ (bin FLessThanEqual (Expr.UnOp (IntToNum, size)) pos);
        ]
      in
      check ~types "rounded guard implies exact index bound" false
        (inside @ [ not_ (bin ILessThan offset size) ]);
      check ~types "canonical complement rejects out of range" false
        (inside @ [ bin ILessThanEqual size offset ]);
      check ~types "checked lookup produces one unit" false
        (inside @ [ not_ (eq (length (bin Utf16Nth a pos)) (Expr.int 1)) ]);
      (* Exercise the refined bound with raw fractional/negative Numbers too.
       The nonnegative guard is necessary: trunc(-0.5) = 0 when N = 0. *)
      List.iter
        (fun (n, p) ->
          let actual = bin ILessThan (Expr.UnOp (NumToInt, Expr.num p)) size in
          let expected = Z.lt (Z.of_float p) n in
          check ~types "exact bound retains rounding boundary" false
            [
              eq size (Expr.Lit (Int n));
              (if expected then not_ actual else actual);
            ];
          check ~types "bound complement retains rounding boundary" false
            [
              eq size (Expr.Lit (Int n));
              (let complement =
                 bin ILessThanEqual size (Expr.UnOp (NumToInt, Expr.num p))
               in
               if expected then complement else not_ complement);
            ])
        [
          (Z.zero, -0.5);
          (Z.zero, -1.);
          (Z.zero, -0.);
          (Z.one, 0.5);
          (Z.of_int 2, 1.5);
          (Z.of_int 65536, 65535.);
          (Z.of_string "9007199254740993", 9007199254740992.);
          (Z.of_string "9007199254740995", 9007199254740996.);
          (Z.shift_left Z.one 1024, Float.max_float);
        ])

let index_conversion_boundaries () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun number ->
      let term = Expr.UnOp (NumToInt, Expr.num number) in
      let expected = Literal.Int (Z.of_float number) in
      Alcotest.(check bool)
        "exact concrete integer conversion" true
        (Literal.equal expected (Engine.CExprEval.evaluate_expr store term));
      check "guarded integer conversion keeps boundary" false
        [ not_ (eq term (Expr.Lit expected)) ])
    [
      -.Float.max_float;
      -65536.5;
      -1.5;
      -0.5;
      -5e-324;
      -0.;
      0.;
      5e-324;
      0.5;
      1.5;
      65535.;
      65535.5;
      65536.;
      65536.5;
      9007199254740992.;
      Float.max_float;
    ]

let index_models () =
  with_total (fun () ->
      let gamma = gamma () in
      Gamma.update gamma "#length_index" NumberType;
      let gamma = Gamma.as_hashtbl gamma in
      let index = Expr.LVar "#length_index" in
      let pos = Expr.UnOp (ToIntOp, index) in
      let nth = bin Utf16Nth a pos in
      let inside =
        [
          not_ (bin FLessThan pos (Expr.num 0.));
          not_ (bin FLessThanEqual (Expr.UnOp (IntToNum, length a)) pos);
        ]
      in
      let models =
        List.map
          (fun (id, extra) ->
            Format.printf "Indexed witness: %s@." id;
            let constraints = inside @ [ eq b nth ] @ extra in
            let model =
              match Smt.exec_sat (Expr.Set.of_list constraints) gamma with
              | Some model -> model
              | None -> Alcotest.fail ("Lost indexed witness: " ^ id)
            in
            let lifted = Hashtbl.create 3 in
            Smt.lift_model model gamma (Hashtbl.add lifted)
              (Expr.Set.of_list [ a; b; index ]);
            let get name =
              match Hashtbl.find_opt lifted name with
              | Some (Expr.Lit value) -> value
              | _ -> Alcotest.fail "Missing indexed model value"
            in
            let bindings =
              List.map
                (fun name -> (name, get name))
                [ "#utf16_a"; "#utf16_b"; "#length_index" ]
            in
            let store = Engine.CExprEval.CStore.init bindings in
            let visitor =
              object
                inherit [_] Visitors.endo
                method! visit_LVar () _ name = Expr.PVar name
              end
            in
            List.iter
              (fun expr ->
                match
                  Engine.CExprEval.evaluate_expr store
                    (visitor#visit_expr () expr)
                with
                | Bool true -> ()
                | _ -> Alcotest.fail "Indexed witness failed concrete replay")
              constraints;
            let units name =
              match get name with
              | Utf16String v ->
                  `List
                    (List.map
                       (fun u -> `Int u)
                       (Codec.code_units (Codec.to_canonical v)))
              | _ -> Alcotest.fail "Indexed witness lost string type"
            in
            let number =
              match get "#length_index" with
              | Num v -> v
              | _ -> Alcotest.fail "Indexed witness lost Number type"
            in
            `Assoc
              [
                ("id", `String id);
                ("units", units "#utf16_a");
                ("resultUnits", units "#utf16_b");
                ( "indexBits",
                  `String (Printf.sprintf "%016Lx" (Int64.bits_of_float number))
                );
              ])
          [
            ("inside", []);
            ( "index-one",
              [
                bin ValueEqual index (Expr.num 1.);
                eq a (value [ 0xd83d; 0xde00 ]);
              ] );
            ("lone-high", [ eq b (value [ 0xd800 ]) ]);
            ("lone-low", [ eq b (value [ 0xdc00 ]) ]);
            ("wrong-unit", [ not_ (eq b (value [ 65 ])) ]);
          ]
      in
      match Sys.getenv_opt "GILLIAN_UTF16_INDEX_MODELS" with
      | None -> ()
      | Some path -> Yojson.Safe.to_file path (`List models))

let checked_code_unit () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun units ->
      List.iteri
        (fun i unit ->
          let term =
            bin Utf16CodeUnit (value units) (Expr.num (float_of_int i))
          in
          let expected = Expr.num (float_of_int unit) in
          Alcotest.(check bool)
            "concrete unsigned code unit" true
            (Expr.equal expected
               (Expr.Lit (Engine.CExprEval.evaluate_expr store term)));
          Alcotest.(check bool)
            "reduced unsigned code unit" true
            (Expr.equal expected (Reduction.reduce_lexpr term));
          with_total (fun () ->
              check "SMT unsigned code unit" false [ not_ (eq term expected) ]))
        units;
      List.iter
        (fun index ->
          let term = bin Utf16CodeUnit (value units) (Expr.num index) in
          let rejected =
            try
              ignore (Engine.CExprEval.evaluate_expr store term);
              false
            with Engine.CExprEval.EvaluationError _ -> true
          in
          Alcotest.(check bool) "invalid code-unit index rejects" true rejected;
          let rejected =
            try
              ignore (Reduction.reduce_lexpr term);
              false
            with Reduction.ReductionException _ -> true
          in
          Alcotest.(check bool)
            "invalid code-unit reduction rejects" true rejected)
        [
          nan;
          infinity;
          neg_infinity;
          -1.;
          0.5;
          float_of_int (List.length units);
          Float.max_float;
        ])
    values;
  with_total (fun () ->
      let term = bin Utf16CodeUnit a (Expr.num 0.) in
      let nonempty = bin ILessThan (Expr.int 0) (length a) in
      check "symbolic unit is a nonnegative finite integer" false
        [
          nonempty;
          not_
            (bin And
               (Expr.UnOp (IsInt, term))
               (bin And
                  (bin FLessThanEqual (Expr.num 0.) term)
                  (bin FLessThanEqual term (Expr.num 65535.))));
        ]);
  let old = !Gillian.Utils.Config.Verification.total in
  Gillian.Utils.Config.Verification.total := false;
  Fun.protect
    ~finally:(fun () -> Gillian.Utils.Config.Verification.total := old)
    (fun () ->
      let rejected =
        try
          ignore
            (Smt.is_sat
               (Expr.Set.of_list
                  [ eq (bin Utf16CodeUnit a (Expr.num 17.)) (Expr.num 4660.) ])
               (Gamma.as_hashtbl (gamma ())));
          false
        with Smt.SMT_error message ->
          String.starts_with ~prefix:"SMT encoding: symbolic UTF-16 indexing"
            message
      in
      Alcotest.(check bool)
        "ordinary symbolic mode rejects unchecked unit lookup" true rejected)

let code_unit_models () =
  with_total (fun () ->
      let old_dump = !Gillian.Utils.Config.dump_smt in
      Gillian.Utils.Config.dump_smt :=
        Option.is_some (Sys.getenv_opt "GILLIAN_UTF16_CODE_MODELS");
      Fun.protect
        ~finally:(fun () -> Gillian.Utils.Config.dump_smt := old_dump)
        (fun () ->
          let gamma = gamma () in
          Gamma.update gamma "#unit_index" NumberType;
          Gamma.update gamma "#unit_result" NumberType;
          let gamma = Gamma.as_hashtbl gamma in
          let index = Expr.LVar "#unit_index" in
          let result = Expr.LVar "#unit_result" in
          let pos = Expr.UnOp (ToIntOp, index) in
          let outside =
            bin Or
              (bin FLessThan pos (Expr.num 0.))
              (bin FLessThanEqual (Expr.UnOp (IntToNum, length a)) pos)
          in
          let models =
            List.map
              (fun (id, inside, extra) ->
                Format.printf "Numeric code-unit witness: %s@." id;
                let constraints =
                  (if inside then
                     [ not_ outside; eq result (bin Utf16CodeUnit a pos) ]
                   else [ outside; bin ValueEqual result (Expr.num nan) ])
                  @ extra
                in
                let model =
                  match Smt.exec_sat (Expr.Set.of_list constraints) gamma with
                  | Some model -> model
                  | None -> Alcotest.fail ("Lost numeric unit witness: " ^ id)
                in
                let lifted = Hashtbl.create 3 in
                Smt.lift_model model gamma (Hashtbl.add lifted)
                  (Expr.Set.of_list [ a; index; result ]);
                let get name =
                  match Hashtbl.find_opt lifted name with
                  | Some (Expr.Lit value) -> value
                  | _ -> Alcotest.fail "Missing numeric unit model value"
                in
                let bindings =
                  List.map
                    (fun name -> (name, get name))
                    [ "#utf16_a"; "#unit_index"; "#unit_result" ]
                in
                let store = Engine.CExprEval.CStore.init bindings in
                let visitor =
                  object
                    inherit [_] Visitors.endo
                    method! visit_LVar () _ name = Expr.PVar name
                  end
                in
                List.iter
                  (fun e ->
                    match
                      Engine.CExprEval.evaluate_expr store
                        (visitor#visit_expr () e)
                    with
                    | Bool true -> ()
                    | _ ->
                        Alcotest.fail
                          "Numeric unit witness failed concrete replay")
                  constraints;
                let bits name =
                  match get name with
                  | Num n ->
                      `String (Printf.sprintf "%016Lx" (Int64.bits_of_float n))
                  | _ -> Alcotest.fail "Numeric unit witness lost Number type"
                in
                let units =
                  match get "#utf16_a" with
                  | Utf16String s ->
                      `List
                        (List.map
                           (fun x -> `Int x)
                           (Codec.code_units (Codec.to_canonical s)))
                  | _ -> Alcotest.fail "Numeric unit witness lost string type"
                in
                `Assoc
                  [
                    ("id", `String id);
                    ("units", units);
                    ("indexBits", bits "#unit_index");
                    ("resultBits", bits "#unit_result");
                  ])
              [
                ("inside", true, [ bin ValueEqual index (Expr.num 0.) ]);
                ( "unsigned-max",
                  true,
                  [
                    bin ValueEqual index (Expr.num 0.);
                    eq result (Expr.num 65535.);
                  ] );
                ( "lone-high",
                  true,
                  [
                    eq a (value [ 0xd800 ]); bin ValueEqual index (Expr.num 0.);
                  ] );
                ( "low-surrogate",
                  true,
                  [
                    eq a (value [ 0xd83d; 0xde00 ]);
                    bin ValueEqual index (Expr.num 1.);
                  ] );
                ( "nan-index",
                  true,
                  [ eq a (value [ 65 ]); bin ValueEqual index (Expr.num nan) ]
                );
                ( "negative-fraction",
                  true,
                  [
                    eq a (value [ 65 ]); bin ValueEqual index (Expr.num (-0.5));
                  ] );
                ( "empty-string",
                  false,
                  [ eq a (value []); bin ValueEqual index (Expr.num 0.) ] );
                ( "positive-infinity",
                  false,
                  [ bin ValueEqual index (Expr.num infinity) ] );
                ( "negative-infinity",
                  false,
                  [ bin ValueEqual index (Expr.num neg_infinity) ] );
                ( "negative-index",
                  false,
                  [ bin ValueEqual index (Expr.num (-1.)) ] );
              ]
          in
          match Sys.getenv_opt "GILLIAN_UTF16_CODE_MODELS" with
          | None -> ()
          | Some path -> Yojson.Safe.to_file path (`List models)))

let tests =
  [
    ("numeric code unit models", `Quick, code_unit_models);
    ("checked numeric code unit", `Quick, checked_code_unit);
    ("checked index domain and bounds", `Quick, checked_index);
    ("index conversion boundaries", `Quick, index_conversion_boundaries);
    ("indexed unit models", `Quick, index_models);
    ("literal domain and transport", `Quick, literal_domain);
    ("concrete and SMT agreement", `Quick, concrete_agreement);
    ("arbitrary typed sequences", `Quick, arbitrary_values);
    ("JS length conversion", `Quick, js_length_conversion);
    ("length conversion boundaries", `Quick, length_conversion_boundaries);
    ("language length integrality", `Quick, language_length_integrality);
    ("length nonnegativity", `Quick, length_nonnegative);
    ("language length bound", `Quick, language_length_bound);
    ("length branch models", `Quick, length_branch_models);
    ("comparison reduction", `Quick, comparison_reduction);
    ("length comparison Numbers", `Quick, length_comparison_numbers);
    ("composition models", `Quick, composition_models);
    ("length model validation", `Quick, length_model_validation);
    ("wrapped values and type identity", `Quick, wrapped_values);
    ("actual lifted models", `Quick, models);
    ("typed numeric producers", `Quick, numeric_producers);
    ("concrete legacy operations", `Quick, concrete_legacy_operations);
    ("expression transport", `Quick, expression_transport);
  ]
