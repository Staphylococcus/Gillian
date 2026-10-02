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
    (* Formatting outside the exact integral Uint32 interval remains an
       over-approximation; concrete reduction still fixes literal results. *)
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
        ~exact_smt:(not (Float.is_finite number)
          || (number >= 0. && number <= 4294967295. && Float.is_integer number))
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

let uint32_formatter_literals () =
  let store = Engine.CExprEval.CStore.init [] in
  let cases = [ -0.; 0.; 4294967294.; 4294967295. ]
      @ List.concat_map (fun power ->
          let n = 10. ** float_of_int power in [ n -. 1.; n; n +. 1. ])
          (List.init 9 (fun i -> i + 1)) in
  List.iter (fun number ->
      let term = Expr.UnOp (NumberToUtf16, Expr.num number) in
      let expected = Expr.Lit (Literal.Utf16String
          (Codec.of_canonical (Printf.sprintf "%.0f" (number +. 0.)))) in
      Alcotest.(check bool) "concrete formatter agrees with decimal integer"
        true (Literal.equal (Engine.CExprEval.evaluate_expr store term)
          (match expected with Expr.Lit l -> l | _ -> assert false));
      check "direct decimal encoding agrees with concrete formatter" false
        [ not_ (eq term expected) ]) cases

let uint32_formatter_indices_checks () =
  let number = Expr.LVar "#decimal_number" in
  let types () =
    let g = Gamma.init () in Gamma.update g "#decimal_number" NumberType; g in
  let formatted = Expr.UnOp (NumberToUtf16, number) in
  let position keys = bin KeyInsertIndex (Expr.EList keys) formatted in
  let text s = Expr.Lit (Literal.Utf16String (Codec.of_canonical s)) in
  let interval = [ Expr.UnOp (IsInt, number);
      bin FLessThanEqual (Expr.num 0.) number;
      bin FLessThan number (Expr.num 4294967295.) ] in
  check ~types "every Uint32 array index precedes ordinary names" false
    (interval @ [ not_ (eq (position [ text "length" ]) (Expr.int 0)) ]);
  check ~types "the excluded Uint32 boundary is an ordinary name" false
    [ eq number (Expr.num 4294967295.);
      not_ (eq (position [ text "length" ]) (Expr.int 1)) ];
  check ~types "a decimal key cannot acquire a leading zero" false
    [ eq number (Expr.num 1.); eq formatted (text "01") ];
  check ~types "a false position claim has a real counterexample" true
    [ eq number (Expr.num 1.);
      not_ (eq (position [ text "length" ]) (Expr.int 1)) ];
  check ~types "both signed zeros give the index zero" false
    [ bin ValueEqual number (Expr.num (-0.));
      not_ (eq formatted (text "0")) ]

let uint32_formatter_indices () =
  let saved = !Gillian.Utils.Config.dump_smt in
  Gillian.Utils.Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Gillian.Utils.Config.dump_smt := saved)
    uint32_formatter_indices_checks

let uint32_formatter_fallback () =
  let term number = Expr.UnOp (NumberToUtf16, Expr.num number) in
  let text s = Expr.Lit (Literal.Utf16String (Codec.of_canonical s)) in
  (* These noncanonical spellings deliberately remain admitted by the opaque
     fallback. They would be ruled out by extending the exact branch past its
     proved integral range, or by truncating an arbitrary Number to Uint32. *)
  List.iter (fun (number, spelling) ->
      Alcotest.(check bool)
        "outside Uint32 the direct SMT formatter remains an over-approximation"
        true (Smt.is_sat (Expr.Set.singleton (eq (term number) (text spelling)))
          (Gamma.as_hashtbl (Gamma.init ()))))
    [ (1.5, "01.5"); (-1., "-01"); (4294967296., "04294967296") ]

let insertion_terminal_bound () =
  let keys = Expr.LVar "#terminal_keys" in
  let number = Expr.LVar "#terminal_number" in
  let types () =
    let g = Gamma.init () in
    Gamma.update g "#terminal_keys" ListType;
    Gamma.update g "#terminal_name" Utf16Type;
    Gamma.update g "#terminal_position" IntType;
    Gamma.update g "#terminal_number" NumberType; g in
  let text s = Expr.Lit (Literal.Utf16String (Codec.of_canonical s)) in
  let len = Expr.UnOp (LstLen, keys) in
  let last = bin LstNth keys (bin IMinus len (Expr.int 1)) in
  let nonempty = bin ILessThanEqual (Expr.int 1) len in
  let position key = bin KeyInsertIndex keys key in
  let before key = bin ILessThan (position key) len in
  let interval = [ Expr.UnOp (IsInt, number);
      bin FLessThanEqual (Expr.num 0.) number;
      bin FLessThan number (Expr.num 4294967295.) ] in
  let checks () =
    let arbitrary_position = position (Expr.LVar "#terminal_name") in
    check ~types "all insertion scans retain a nonnegative position" false
      [ not_ (bin ILessThanEqual (Expr.int 0) arbitrary_position) ];
    check ~types "all insertion scans retain a position at most list length"
      false [ not_ (bin ILessThanEqual arbitrary_position len) ];
    let p = Expr.LVar "#terminal_position" in
    let inserted = Expr.NOp (LstInsert, [ keys; p; Expr.EList [] ]) in
    check ~types "insertion before the end preserves an arbitrary final element"
      false [ bin ILessThanEqual (Expr.int 0) p; bin ILessThan p len;
        not_ (bin ValueEqual (bin LstNth inserted len) last) ];
    List.iter (fun (label, list, position) ->
        let inserted = Expr.NOp (LstInsert, [ keys; Expr.int position; Expr.EList [] ]) in
        check ~types label true [ bin ValueEqual keys (Expr.EList list);
          bin ValueEqual (bin LstNth inserted len) (Expr.EList []) ])
      [ "append leaves the new element last", [text "length"], 1;
        "insertion into empty leaves the new element last", [], 0 ];
    check ~types "every allowed index stops before an arbitrary final length cell"
      false (interval @ [ nonempty; bin ValueEqual last (text "length");
        not_ (before (Expr.UnOp (NumberToUtf16, number))) ]);
    check ~types "a larger final index also stops the finite scan" false
      [ nonempty; bin ValueEqual last (text "3"); not_ (before (text "2")) ];
    check ~types "a non-UTF16 final element stops without inventing its type"
      false [ nonempty; bin ValueEqual last (Expr.num 7.);
        not_ (before (text "0")) ];
    (* Each disabled guard has an actual position == length witness. A
       blanket strict bound would erase these SAT models. *)
    List.iter (fun (label, list, key) ->
        check ~types label true [ bin ValueEqual keys (Expr.EList list);
          eq (position key) len ])
      [ "empty list retains the append position", [], text "0";
        "ordinary inserted names retain append", [ text "length" ], text "z";
        "the excluded Uint32 boundary retains append", [ text "length" ],
          text "4294967295";
        "a smaller terminal index retains append", [ text "1" ], text "2";
        "an equal terminal index retains append", [ text "2" ], text "2" ];
    let store = Engine.CExprEval.CStore.init [] in
    List.iter (fun (list, key, expected) ->
        let term = bin KeyInsertIndex (Expr.EList list) key in
        Alcotest.(check bool) "terminal bound agrees with concrete insertion" true
          (Literal.equal (Engine.CExprEval.evaluate_expr store term)
             (Literal.Int (Z.of_int expected))))
      [ [text "0"; text "length"], text "2", 1;
        [text "3"; text "length"], text "2", 0;
        [text "0"; Expr.num 7.], text "2", 1 ]
  in
  let saved = !Gillian.Utils.Config.dump_smt in
  Gillian.Utils.Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Gillian.Utils.Config.dump_smt := saved) checks

let insertion_array_width () =
  let xs = Expr.LVar "#width_list" and p = Expr.LVar "#width_position" in
  let types () =
    let g = Gamma.init () in
    Gamma.update g "#width_list" ListType;
    Gamma.update g "#width_position" IntType; g in
  let len = Expr.UnOp (LstLen, xs) in
  let inserted = Expr.NOp (LstInsert, [ xs; p; Expr.EList [] ]) in
  let after = Expr.UnOp (LstLen, inserted) in
  let bounds = [ bin ILessThanEqual (Expr.int 0) p;
      bin ILessThanEqual p len ] in
  let context assumptions =
    let pfs = Gillian.Symbolic.Pure_context.init () in
    List.iter (Gillian.Symbolic.Pure_context.extend pfs) assumptions; pfs in
  let reduced assumptions = Reduction.reduce_lexpr ~gamma:(types ())
      ~pfs:(context assumptions) after in
  let successor = Reduction.reduce_lexpr ~gamma:(types ())
      (bin IPlus len (Expr.int 1)) in
  let unchanged = reduced [] in
  Alcotest.(check bool) "proved insertion bounds canonicalize its length" true
    (Expr.equal (reduced bounds) successor);
  Alcotest.(check bool) "unknown bounds cannot authorize the successor" false
    (Expr.equal unchanged successor);
  List.iter (fun assumptions ->
      Alcotest.(check bool) "missing insertion bound preserves the operation"
        true (Expr.equal (reduced assumptions) unchanged))
    [ []; [ List.hd bounds ]; [ List.nth bounds 1 ] ];
  let position = bin KeyInsertIndex xs (value [ 48 ]) in
  let scan_insert = Expr.UnOp (LstLen, Expr.NOp (LstInsert,
      [ xs; position; Expr.EList [] ])) in
  Alcotest.(check bool) "typed scan bounds canonicalize insertion length" true
    (Expr.equal (Reduction.reduce_lexpr ~gamma:(types ()) scan_insert)
      successor);
  Alcotest.(check bool) "missing list type cannot authorize length reduction"
    false (try Expr.equal (Reduction.reduce_lexpr scan_insert)
      successor
      with Reduction.ReductionException _ -> false);
  check ~types "in-range insertion preserves the complete array-width bound"
    false (bounds @ [ bin ILessThanEqual len (Expr.int 4294967295);
      bin ILessThan (Expr.int 4294967296) after ]);
  check ~types "the maximum footprint retains its exact successor"
    false (bounds @ [ eq len (Expr.int 4294967295);
      eq p len; not_ (eq after (Expr.int 4294967296)) ]);
  List.iter (fun (count, position) ->
      let list = Expr.EList (List.init count (fun _ -> Expr.bool true)) in
      let term = Expr.NOp (LstInsert, [ list; Expr.int position; Expr.EList [] ]) in
      let expected = Literal.Int (Z.of_int (count + 1)) in
      Alcotest.(check bool) "endpoint/interior lengths agree with concrete insertion"
        true (Literal.equal expected
          (Engine.CExprEval.evaluate_expr (Engine.CExprEval.CStore.init [])
            (Expr.UnOp (LstLen, term)))))
    [ 0, 0; 1, 0; 1, 1; 2, 1; 2, 2 ];
  (* Outside the GIL operation's domain, only inspect the SMT encoding. The
     ordinary reducer must keep rejecting this invalid insertion. *)
  Alcotest.(check bool) "negative indices do not acquire an unguarded length identity"
    true (Smt.is_sat (Expr.Set.of_list
      [ eq xs (Expr.EList [ Expr.bool true; Expr.bool false ]);
        eq p (Expr.int (-1)); not_ (eq after (bin IPlus len (Expr.int 1))) ])
      (Gamma.as_hashtbl (types ())));
  check ~types "a false insertion length has a genuine countermodel" true
    [ eq xs (Expr.EList []); eq p (Expr.int 0);
      not_ (eq after (Expr.int 2)) ]

let insertion_terminal_reduction () =
  let keys = Expr.LVar "#transfer_keys" and values = Expr.LVar "#transfer_values" in
  let key = Expr.LVar "#transfer_key" and old = Expr.LVar "#transfer_old" in
  let types () =
    let g = Gamma.init () in
    List.iter (fun name -> Gamma.update g name ListType)
      [ "#transfer_keys"; "#transfer_values" ];
    Gamma.update g "#transfer_key" Utf16Type;
    Gamma.update g "#transfer_old" NumberType; g in
  let len = Expr.UnOp (LstLen, keys) in
  let last_index = bin IPlus (Expr.int (-1)) len in
  let old_descriptor = bin LstNth values last_index in
  let text s = Expr.Lit (Literal.Utf16String (Codec.of_canonical s)) in
  let descriptor = Expr.EList [ text "d"; old; Expr.bool true;
    Expr.bool false; Expr.bool false ] in
  let number = Expr.UnOp (Utf16ToNumber, key) in
  let position = bin KeyInsertIndex keys key in
  let inserted = Expr.NOp (LstInsert, [ values; position; Expr.EList [] ]) in
  let read = bin LstNth (bin LstNth inserted len) (Expr.int 1) in
  let assumptions = [
    bin ILessThanEqual (Expr.int 1) len;
    eq (bin LstNth keys last_index) (text "length");
    eq key (Expr.UnOp (NumberToUtf16, number));
    Expr.UnOp (IsInt, number);
    bin FLessThanEqual (Expr.num 0.) number;
    bin FLessThan number (Expr.num 4294967295.);
    eq len (Expr.UnOp (LstLen, values));
    bin ValueEqual old_descriptor descriptor ] in
  let context assumptions =
    let pfs = Gillian.Symbolic.Pure_context.init () in
    List.iter (Gillian.Symbolic.Pure_context.extend pfs) assumptions; pfs in
  let reduce ?(gamma = types ()) assumptions e =
    Reduction.reduce_lexpr ~gamma ~pfs:(context assumptions) e in
  Alcotest.(check bool) "key/descriptor length alias preserves the old Number witness"
    true (Expr.equal (reduce assumptions read) old);
  Alcotest.(check bool) "preserved descriptor type is proved structurally"
    true (Expr.equal (reduce assumptions
      (eq (Expr.UnOp (TypeOf, read)) (Expr.Lit (Literal.Type NumberType)))) Expr.true_);
  List.iteri (fun omitted _ ->
    let fewer = List.filteri (fun i _ -> i <> omitted) assumptions in
    Alcotest.(check bool) "every terminal transfer premise is required" false
      (try Expr.equal (reduce fewer read) old
       with Reduction.ReductionException _ -> false)) assumptions;
  List.iter (fun name ->
    let g = types () in Gamma.remove g name;
    Alcotest.(check bool) "missing input type cannot authorize terminal transfer"
      false (try Expr.equal (reduce ~gamma:g assumptions read) old
        with Reduction.ReductionException _ -> false))
    [ "#transfer_keys"; "#transfer_values"; "#transfer_key" ];
  let p = Expr.LVar "#transfer_position" in
  let len_values = Expr.UnOp (LstLen, values) in
  let end_read = bin LstNth
    (Expr.NOp (LstInsert, [ values; p; Expr.bool false ])) len_values in
  let before = [ bin ILessThanEqual (Expr.int 0) p;
    bin ILessThan p len_values ] in
  let g = types () in Gamma.update g "#transfer_position" IntType;
  let expected = bin LstNth values (bin IPlus (Expr.int (-1)) len_values) in
  Alcotest.(check bool) "explicit strict insertion bounds transfer the final element"
    true (Expr.equal (reduce ~gamma:g before end_read) expected);
  List.iter (fun bounds ->
    Alcotest.(check bool) "missing or append bound cannot transfer the old last value"
      false (Expr.equal (reduce ~gamma:g bounds end_read) expected))
    [ []; [ List.hd before ]; [ List.nth before 1 ];
      [ List.hd before; bin ILessThanEqual p len_values ] ];
  let zero_descriptor = Expr.EList [ Expr.num (-0.) ] in
  Alcotest.(check bool) "value identity retains the sign of a fixed component"
    true (Expr.equal (reduce [ bin ValueEqual old_descriptor zero_descriptor ]
      (bin LstNth old_descriptor (Expr.int 0))) (Expr.num (-0.)));
  let saved = !Gillian.Utils.Config.Verification.total in
  Gillian.Utils.Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Gillian.Utils.Config.Verification.total := saved)
    (fun () ->
      let invalid = bin LstNth (Expr.EList []) (Expr.int 0) in
      Alcotest.(check bool) "terminal transfer cannot erase a failing insertion value"
        true (try ignore (reduce assumptions (bin LstNth
          (Expr.NOp (LstInsert, [ values; position; invalid ])) len)); false
          with Reduction.ReductionException _ -> true))

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
      check "ToInt32 preserves an arbitrary numeric code unit" false
        [ nonempty; not_ (eq (Expr.UnOp (ToInt32Op, term)) term) ];
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
        "ordinary symbolic mode rejects unchecked unit lookup" true rejected;
      let rejected_composite =
        try
          ignore
            (Smt.is_sat
               (Expr.Set.singleton
                  (eq
                     (Expr.UnOp (ToInt32Op, bin Utf16CodeUnit a (Expr.num 17.)))
                     (Expr.num 4660.)))
               (Gamma.as_hashtbl (gamma ())));
          false
        with Smt.SMT_error message ->
          String.starts_with ~prefix:"SMT encoding: symbolic UTF-16 indexing"
            message
      in
      Alcotest.(check bool)
        "ToInt32 cannot bypass the ordinary lookup gate" true rejected_composite)

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

let uint32_integer_successor_checks () =
  with_total (fun () ->
    let number = Expr.LVar "#uint32_successor" in
    let types () =
      let g = Gamma.init () in
      Gamma.update g "#uint32_successor" Type.NumberType;
      g in
    let integer e = Expr.UnOp (NumToInt, e) in
    let successor = bin FPlus number (Expr.num 1.) in
    let identity = eq (integer successor)
      (bin IPlus (integer number) (Expr.int 1)) in
    check ~types "full Uint32 natural successor preserves exact integer count"
      false [ Expr.UnOp (IsInt, number);
        bin FLessThanEqual (Expr.num 0.) number;
        bin FLessThan number (Expr.num 4294967295.);
        not_ identity ];
    check ~types "without integrality rounding has a real counterexample" true
      [ eq number (Expr.num (Float.pred 1.)); not_ identity ];
    check ~types "without the bound a large integer cannot advance" true
      [ eq number (Expr.num 9007199254740992.); not_ identity ];
    let store = Engine.CExprEval.CStore.init [] in
    List.iter (fun n ->
      let term = integer (Expr.num n) in
      let expected = Expr.Lit (Literal.Int (Z.of_float n)) in
      Alcotest.(check bool) "concrete truncation agrees at all branch boundaries"
        true (Literal.equal
          (Engine.CExprEval.evaluate_expr store term)
          (match expected with Expr.Lit l -> l | _ -> assert false));
      check "guarded native truncation keeps fallback and fractional values"
        false [ not_ (eq term expected) ])
      [ -65536.5; -0.; 0.; 65535.5; 65536.; 65536.5;
        4294967294.; 4294967295.; 4294967295.5;
        4294967296.; 4294967296.5; 9007199254740992. ])

let uint32_integer_successor () =
  let saved = !Gillian.Utils.Config.dump_smt in
  Gillian.Utils.Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Gillian.Utils.Config.dump_smt := saved)
    uint32_integer_successor_checks

let dense_index_step () =
  with_total (fun () ->
    let head = Expr.LVar "#dense_head" and target = Expr.LVar "#dense_target" in
    let tail = Expr.LVar "#dense_tail" in
    let types () =
      let g = Gamma.init () in
      Gamma.update g "#dense_head" NumberType;
      Gamma.update g "#dense_target" NumberType;
      Gamma.update g "#dense_tail" ListType; g in
    let text s = Expr.Lit (Literal.Utf16String (Codec.of_canonical s)) in
    let format n = Expr.UnOp (NumberToUtf16, n) in
    let suffix = Expr.NOp (LstCat, [ tail; Expr.EList [text "length"] ]) in
    let keys = Expr.NOp (LstCat,
      [Expr.EList [format head]; tail; Expr.EList [text "length"]]) in
    let position = bin KeyInsertIndex keys (format target) in
    let expected = bin IPlus (Expr.int 1)
      (bin KeyInsertIndex suffix (format target)) in
    let premises = [ Expr.UnOp (IsInt, head); Expr.UnOp (IsInt, target);
      bin FLessThanEqual (Expr.num 0.) head;
      bin FLessThan head target;
      bin FLessThan target (Expr.num 4294967295.) ] in
    let context facts =
      let pfs = Gillian.Symbolic.Pure_context.init () in
      List.iter (Gillian.Symbolic.Pure_context.extend pfs) facts; pfs in
    let reduce ?(gamma = types ()) facts e =
      Reduction.reduce_lexpr ~gamma ~pfs:(context facts) e in
    let authorizes ?(gamma = types ()) facts =
      try
        let actual = reduce ~gamma:(Gamma.copy gamma) facts position in
        let wanted = reduce ~gamma:(Gamma.copy gamma) facts expected in
        Expr.equal actual wanted
      with Reduction.ReductionException _ -> false in
    Alcotest.(check bool) "canonical smaller head advances exactly one scan step"
      true (authorizes premises);
    Alcotest.(check bool) "an equal canonical head also advances one step" true
      (authorizes [ Expr.UnOp (IsInt, head); Expr.UnOp (IsInt, target);
        bin FLessThanEqual (Expr.num 0.) head;
        bin FLessThanEqual head target;
        bin FLessThan target (Expr.num 4294967295.) ]);
    let next = bin FPlus head (Expr.num 1.) in
    let two_heads = bin KeyInsertIndex (Expr.NOp (LstCat,
      [Expr.EList [format head; format next]; tail; Expr.EList [text "length"]]))
      (format target) in
    let next_facts = [Expr.UnOp (IsInt, next);
      bin FLessThanEqual (Expr.num 0.) next; bin FLessThan next target] in
    let two_expected = bin IPlus (Expr.int 2)
      (bin KeyInsertIndex suffix (format target)) in
    let two_actual = reduce (premises @ next_facts) two_heads in
    Alcotest.(check bool) "checked numeric successor heads advance two scan steps"
      true (Expr.equal two_actual (reduce (premises @ next_facts) two_expected));
    let unknown = Expr.LVar "#unknown_suffix_number" in
    let unsafe_suffix = bin KeyInsertIndex (Expr.NOp (LstCat,
      [Expr.EList [format head; format unknown]; tail])) (format target) in
    Alcotest.(check bool) "a formatted suffix needs its original Number type"
      true (try
        let result = reduce premises unsafe_suffix in
        let visitor = object
          inherit [_] Visitors.iter as super
          val mutable found = false
          method found = found
          method! visit_expr () e =
            (match e with Expr.BinOp (_, KeyInsertIndex, _) -> found <- true
             | _ -> ()); super#visit_expr () e
        end in
        visitor#visit_expr () result; visitor#found
        with Reduction.ReductionException _ -> true);
    List.iteri (fun omitted _ ->
      Alcotest.(check bool) "each range/integrality/order premise is required"
        false (authorizes (List.filteri (fun i _ -> i <> omitted) premises))) premises;
    List.iter (fun name ->
      let g = types () in Gamma.remove g name;
      Alcotest.(check bool) ("missing input type cannot authorize a scan step: " ^ name)
        false (authorizes ~gamma:g premises))
      [ "#dense_head"; "#dense_target"; "#dense_tail" ];
    let stop = bin KeyInsertIndex (Expr.EList [text "length"])
      (format target) in
    let range = [ Expr.UnOp (IsInt, target);
      bin FLessThanEqual (Expr.num 0.) target;
      bin FLessThan target (Expr.num 4294967295.) ] in
    Alcotest.(check bool) "ordinary length stops every allowed array index"
      true (Expr.equal (reduce range stop) (Expr.int 0));
    Alcotest.(check bool) "nonnegativity follows a typed equal range witness"
      true (Expr.equal (reduce
        [ Expr.UnOp (IsInt, target); eq head target;
          bin FLessThanEqual (Expr.num 0.) head;
          bin FLessThan target (Expr.num 4294967295.) ] stop) (Expr.int 0));
    List.iteri (fun omitted _ ->
      Alcotest.(check bool) "ordinary-key stop requires each range premise"
        false (try Expr.equal (reduce
          (List.filteri (fun i _ -> i <> omitted) range) stop) (Expr.int 0)
          with Reduction.ReductionException _ -> false)) range;
    let shadowed binder_type =
      Expr.ForAll (["#dense_target", binder_type],
        List.fold_right (fun fact body -> bin Impl fact body) range
          (eq stop (Expr.int 0))) in
    Alcotest.(check bool) "shadowed input cannot borrow the outer Number type"
        true (try
          let result = reduce [] (shadowed None) in
          let retained = ref false in
          let visitor = object
            inherit [_] Visitors.iter as super
            method! visit_expr () e =
              (match e with Expr.BinOp (_, KeyInsertIndex, _) -> retained := true
               | _ -> ());
              super#visit_expr () e
          end in
          visitor#visit_expr () result;
          !retained
          with Reduction.ReductionException _ -> true);
    Alcotest.(check bool) "declared binder Number type authorizes the guarded step"
      true (Expr.equal (reduce [] (shadowed (Some NumberType))) Expr.true_);
    let failing_tail = Expr.LstSub (tail, Expr.int (-1), Expr.int 1) in
    let failing = bin KeyInsertIndex
      (Expr.NOp (LstCat, [Expr.EList [text "length"]; failing_tail]))
      (format target) in
    Alcotest.(check bool) "an ordinary-key stop cannot erase a failing slice"
      true (try
        let result = reduce range failing in
        let retained = ref false in
        let visitor = object
          inherit [_] Visitors.iter as super
          method! visit_expr () e =
            if Expr.equal e failing_tail then retained := true;
            super#visit_expr () e
        end in
        visitor#visit_expr () result;
        !retained && not (Expr.equal result (Expr.int 0))
        with Reduction.ReductionException _ -> true);
    let store = Engine.CExprEval.CStore.init [] in
    List.iter (fun (n, m, expected) ->
      let term = bin KeyInsertIndex
        (Expr.EList [ format (Expr.num n); text "length" ])
        (format (Expr.num m)) in
      Alcotest.(check bool) "boundary/fallback positions agree with concrete semantics"
        true (Literal.equal (Engine.CExprEval.evaluate_expr store term)
          (Literal.Int (Z.of_int expected))))
      [ -0., 0., 1; 0., -0., 1; 1., 2., 1; 9., 10., 1;
        65535., 65536., 1; 4294967293., 4294967294., 1;
        4294967294., 4294967294., 1; 2., 1., 0;
        0., 4294967295., 2; 1.5, 2., 0; -1., 0., 0 ])

let uint32_count_bounds_checks () =
  with_total (fun () ->
    let number = Expr.LVar "#uint32_count" in
    let types () =
      let g = Gamma.init () in
      Gamma.update g "#uint32_count" Type.NumberType; g in
    let integer = Expr.UnOp (NumToInt, number) in
    let range = [Expr.UnOp (IsInt, number);
      bin FLessThanEqual (Expr.num 0.) number;
      bin FLessThan number (Expr.num 4294967295.)] in
    check ~types "every dense Array length converts to a nonnegative count"
      false (bin ILessThan integer (Expr.int 0) :: range);
    check ~types "every appendable Array length is below the final count"
      false (bin ILessThan (Expr.int 4294967294) integer :: range);
    check ~types "without nonnegativity a negative count is possible"
      true [eq number (Expr.num (-1.)); bin ILessThan integer (Expr.int 0)];
    check ~types "without the upper bound final length cannot be appended"
      true [eq number (Expr.num 4294967295.);
        bin ILessThan (Expr.int 4294967294) integer];
    let store = Engine.CExprEval.CStore.init [] in
    List.iter (fun n ->
      let term = Expr.UnOp (NumToInt, Expr.num n) in
      let expected = Expr.Lit (Literal.Int (Z.of_float n)) in
      Alcotest.(check bool) "UInt32 encoding and fallback match concrete truncation"
        true (Literal.equal (Engine.CExprEval.evaluate_expr store term)
          (match expected with Expr.Lit l -> l | _ -> assert false));
      check "literal truncation cannot be replaced by a constant or modular wrap"
        false [not_ (eq term expected)])
      [-1.; -0.5; -0.; 0.; 0.5; 65535.5; 65536.; 65536.5;
       4294967294.; 4294967295.; 4294967295.5;
       4294967296.; 4294967296.5; 9007199254740992.])

let uint32_count_bounds () =
  let saved = !Gillian.Utils.Config.dump_smt in
  Gillian.Utils.Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Gillian.Utils.Config.dump_smt := saved)
    uint32_count_bounds_checks

let integer_count_alias () =
  with_total (fun () ->
    let left = Expr.LVar "#a_count" and right = Expr.LVar "#z_count" in
    let gamma () =
      let g = Gamma.init () in
      Gamma.update g "#a_count" NumberType;
      Gamma.update g "#z_count" NumberType; g in
    let premises = [eq left right; Expr.UnOp (IsInt,left); Expr.UnOp (IsInt,right)] in
    let context facts =
      let pfs = Gillian.Symbolic.Pure_context.init () in
      List.iter (Gillian.Symbolic.Pure_context.extend pfs) facts; pfs in
    let count e = Expr.UnOp (NumToInt, e) in
    let reduce ?(g = gamma ()) ?(facts = premises) e =
      Reduction.reduce_lexpr ~pfs:(context facts) ~gamma:g e in
    Alcotest.(check bool) "equal finite Number atoms share an integer count"
      true (Expr.equal (reduce (count right)) (count left));
    List.iter (fun omitted ->
      let g = gamma () in Gamma.remove g omitted;
      Alcotest.(check bool) "both original Number types are required"
        true (Expr.equal (reduce ~g (count right)) (count right)))
      ["#a_count"; "#z_count"];
    List.iteri (fun omitted _ ->
      Alcotest.(check bool) "equality and both finite-domain premises are required"
        true (Expr.equal (reduce ~facts:(List.filteri (fun i _ -> i<>omitted) premises)
          (count right)) (count right))) premises;
    let partial = bin LstNth (Expr.EList []) (Expr.int 0) in
    let partial_term = count partial in
    Alcotest.(check bool) "a failing indexed operand is not replaced" true
      (try ignore (reduce ~facts:[eq partial left] partial_term); false
       with Reduction.ReductionException _ -> true);
    Alcotest.(check bool) "a partial equality witness is never selected" true
      (Expr.equal (reduce ~facts:[eq right partial; Expr.UnOp (IsInt,right)]
        (count right)) (count right));
    let scoped binding = Expr.ForAll (["#z_count",binding],
      List.fold_right (fun p e -> bin Impl p e) premises
        (eq (count right) (count left))) in
    Alcotest.(check bool) "an untyped shadow cannot borrow its outer Number type"
      false (Expr.equal (reduce (scoped None)) Expr.true_);
    Alcotest.(check bool) "a declared Number binder permits the finite rewrite"
      true (Expr.equal (reduce (scoped (Some NumberType))) Expr.true_);
    let visitor = object
      inherit [_] Visitors.endo
      method! visit_LVar () _ name = Expr.PVar name
    end in
    List.iter (fun (a,b) ->
      let store=Engine.CExprEval.CStore.init
        ["#a_count",Literal.Num a; "#z_count",Literal.Num b] in
      let evaluate e = Engine.CExprEval.evaluate_expr store (visitor#visit_expr () e) in
      Alcotest.(check bool) "numeric aliases preserve count including signed zeros"
        true (Literal.equal (evaluate (count right)) (evaluate (reduce (count right)))))
      [0.,-0.; -0.,0.; 65536.,65536.; 4294967294.,4294967294.;
       4294967295.,4294967295.; 4294967296.,4294967296.;
       -1.,-1.; 9007199254740992.,9007199254740992.];
    List.iter (fun n ->
      let term=reduce ~facts:[eq left right] (count right) in
      let store=Engine.CExprEval.CStore.init
        ["#a_count",Literal.Num n; "#z_count",Literal.Num n] in
      Alcotest.(check bool) "nonfinite conversion is retained and still rejected"
        true (Expr.equal term (count right) &&
          (try ignore (Engine.CExprEval.evaluate_expr store
            (visitor#visit_expr () term)); false with _ -> true)))
      [infinity;neg_infinity])

let utf16_list_concatenation () =
  with_total (fun () ->
    let names = Expr.LVar "#typed_names" and key = Expr.LVar "#typed_key" in
    let number = Expr.LVar "#typed_number" in
    let gamma () =
      let g = Gamma.init () in
      Gamma.update g "#typed_names" ListType;
      Gamma.update g "#typed_key" Utf16Type;
      Gamma.update g "#typed_number" NumberType; g in
    let all e = Expr.UnOp (LstAllUtf16,e) in
    let concat xs = Expr.NOp (LstCat,xs) in
    let length_key = value [108;101;110;103;116;104] in
    let old = all (concat [names;Expr.EList [length_key]]) in
    let grown = all (concat [names;Expr.EList [key;length_key]]) in
    let reduce ?(g=gamma ()) e = Reduction.reduce_lexpr ~gamma:g e in
    Alcotest.(check bool) "all typed concatenated keys reduce to the prefix predicate"
      true (Expr.equal (reduce grown) (all names));
    Alcotest.(check bool) "original prefix typing has the same normal form"
      true (Expr.equal (reduce old) (all names));
    Alcotest.(check bool) "the actual abstract grown-key obligation is UNSAT"
      false (Solver.check_satisfiability [old;not_ grown] (gamma ()));
    let formatted = all (concat [names;
      Expr.EList [Expr.UnOp (NumberToUtf16,number);length_key]]) in
    Alcotest.(check bool) "total Number formatting preserves UTF16 element typing"
      true (Expr.equal (reduce formatted) (all names));
    let retains_concat e =
      let retained = ref false in
      let visitor = object
        inherit [_] Visitors.iter as super
        method! visit_expr () e =
          (match e with Expr.UnOp (LstAllUtf16,Expr.NOp (LstCat,_)) -> retained:=true
           | _ -> ()); super#visit_expr () e
      end in visitor#visit_expr () e; !retained in
    List.iter (fun name ->
      let g=gamma () in Gamma.remove g name;
      Alcotest.(check bool) "missing original List/value typing blocks the shortcut"
        true (try retains_concat (reduce ~g grown)
          with Reduction.ReductionException _ -> true))
      ["#typed_names";"#typed_key"];
    let g=gamma () in Gamma.remove g "#typed_number";
    Alcotest.(check bool) "untyped formatted values cannot borrow inferred types"
      true (try retains_concat (reduce ~g formatted)
        with Reduction.ReductionException _ -> true);
    let bad_prefix = Expr.EList [Expr.num 3.] in
    let partials = [Expr.LstSub(names,Expr.int (-1),Expr.int 1);
      Expr.EList [bin LstNth (Expr.EList []) (Expr.int 0)]] in
    List.iter (fun partial ->
      let term=all(concat [bad_prefix;partial]) in
      Alcotest.(check bool) "a false prefix cannot erase a failing later operand"
        true (try let result=reduce term in
          retains_concat result && not (Expr.equal result Expr.false_)
          with Reduction.ReductionException _ -> true)) partials;
    Alcotest.(check bool) "a complete non-UTF16 list is genuinely false"
      true (Expr.equal (reduce (all(concat [bad_prefix;Expr.EList [key]]))) Expr.false_);
    let scoped binding = Expr.ForAll(["#typed_names",binding],
      eq grown (all names)) in
    Alcotest.(check bool) "an untyped shadow cannot borrow the outer List type"
      true (try retains_concat (reduce (scoped None))
        with Reduction.ReductionException _ -> true);
    Alcotest.(check bool) "a declared List binder permits the exact split"
      true (Expr.equal (reduce (scoped (Some ListType))) Expr.true_);
    let store=Engine.CExprEval.CStore.init [] in
    List.iter (fun units ->
      let text=value units in
      List.iter (fun suffix ->
        let term=all(concat [Expr.EList [text];Expr.EList suffix]) in
        let concrete=Engine.CExprEval.evaluate_expr store term in
        Alcotest.(check bool) "concrete UTF16, lone-surrogate and false lists agree"
          true (Expr.equal (reduce term) (Expr.Lit concrete)))
        [[];[text;length_key];[Expr.num (-0.)];[Expr.num 0.];
         [Expr.Lit Literal.Null];[Expr.true_]]) values;
    List.iter (fun n ->
      let term=all(concat [Expr.EList [Expr.UnOp(NumberToUtf16,Expr.num n)];
        Expr.EList [length_key]]) in
      Alcotest.(check bool) "formatting is total for both zeros and nonfinite Numbers"
        true (Expr.equal (reduce term) Expr.true_ &&
          Literal.equal (Engine.CExprEval.evaluate_expr store term) (Literal.Bool true)))
      [-0.;0.;nan;infinity;neg_infinity])

let checked_prefix_splice () =
  with_total (fun () ->
    let names=Expr.LVar "#splice_names" and payload=Expr.LVar "#splice_values" in
    let number=Expr.LVar "#splice_number" and item=Expr.LVar "#splice_value" in
    let gamma () = let g=Gamma.init () in
      List.iter (fun x -> Gamma.update g x ListType) ["#splice_names";"#splice_values"];
      Gamma.update g "#splice_number" NumberType;
      Gamma.update g "#splice_value" BooleanType; g in
    let len e=Expr.UnOp(LstLen,e) in
    let concat xs=Expr.NOp(LstCat,xs) in
    let text s=Expr.Lit(Literal.Utf16String(Codec.of_canonical s)) in
    let key=Expr.UnOp(NumberToUtf16,number) in
    let keys=concat [names;Expr.EList [text "length"]] in
    let position=bin KeyInsertIndex keys key in
    let descriptor=Expr.EList [text "d";item;Expr.true_;Expr.true_;Expr.true_] in
    let length_descriptor n=Expr.EList [text "d";n;Expr.true_;Expr.false_;Expr.false_] in
    let values=concat [payload;Expr.EList [length_descriptor number]] in
    let insert xs v=Expr.NOp(LstInsert,[xs;position;v]) in
    let premises=[Expr.UnOp(LstAllUtf16,names);eq position (len names);
      eq (len names) (len payload)] in
    let context facts=let pfs=Gillian.Symbolic.Pure_context.init () in
      List.iter (Gillian.Symbolic.Pure_context.extend pfs) facts;pfs in
    let reduce ?(g=gamma ()) ?(facts=premises) e =
      Reduction.reduce_lexpr ~gamma:g ~pfs:(context facts) e in
    let wanted_keys=concat [names;Expr.EList [key;text "length"]] in
    let wanted_values=concat [payload;Expr.EList [descriptor;length_descriptor number]] in
    Alcotest.(check bool) "checked key position inserts before the literal length key"
      true (Expr.equal (reduce (insert keys key)) (reduce wanted_keys));
    Alcotest.(check bool) "equal key/descriptor counts preserve their distinct sequences"
      true (Expr.equal (reduce (insert values descriptor)) (reduce wanted_values));
    let inserted_keys=insert keys key and inserted_values=insert values descriptor in
    let next=bin FPlus number (Expr.num 1.) in
    let after=concat [
      Expr.LstSub(inserted_values,Expr.int 0,
        bin IMinus (len inserted_keys) (Expr.int 1));
      Expr.EList [length_descriptor (bin FPlus next (Expr.num 0.))];
      Expr.LstSub(inserted_values,len inserted_keys,
        bin IMinus (len inserted_values) (len inserted_keys))] in
    let expected=concat[payload;Expr.EList[descriptor;length_descriptor next]] in
    let range=[Expr.UnOp(IsInt,number);bin FLessThanEqual (Expr.num 0.) number;
      bin FLessThan number (Expr.num 4294967295.)] in
    Alcotest.(check bool) "the actual grown writer slices equal the appended payload"
      false (Solver.check_satisfiability (not_(eq after expected)::premises@range)
        (gamma ()));
    let retained e = match reduce e with Expr.NOp(LstInsert,_) -> true | _ -> false in
    List.iteri (fun omitted _ ->
      Alcotest.(check bool) "each position/domain/count witness remains load-bearing"
        true (match reduce ~facts:(List.filteri(fun i _ -> i<>omitted) premises)
          (insert values descriptor) with Expr.NOp(LstInsert,_) -> true | _ -> false)) premises;
    List.iter (fun x ->
      let g=gamma () in Gamma.remove g x;
      Alcotest.(check bool) "original list/key/value types are required by the splice"
        true (try match reduce ~g (insert values descriptor) with
          Expr.NOp(LstInsert,_) -> true | _ -> false
          with Reduction.ReductionException _ -> true))
      ["#splice_names";"#splice_values";"#splice_number";"#splice_value"];
    let partial=bin LstNth (Expr.EList []) (Expr.int 0) in
    Alcotest.(check bool) "a failing inserted descriptor is not hidden" true
      (try ignore(reduce (insert values partial));false
       with Reduction.ReductionException _ -> true);
    Alcotest.(check bool) "a failing position cannot be replaced by its equal witness" true
      (try let p=partial in
        ignore(reduce ~facts:(eq p (len names)::premises)
          (Expr.NOp(LstInsert,[keys;p;key])));false
       with Reduction.ReductionException _ -> true);
    Alcotest.(check bool) "an unrelated insertion position is retained" true
      (retained (Expr.NOp(LstInsert,[keys;Expr.int 0;key])));
    let scoped ty=Expr.ForAll(["#splice_values",ty],
      List.fold_right(fun fact body -> bin Impl fact body) premises
        (eq (insert values descriptor) wanted_values)) in
    Alcotest.(check bool) "an untyped shadow cannot inherit the descriptor-list type"
      false (Expr.equal (reduce (scoped None)) Expr.true_);
    Alcotest.(check bool) "an explicitly typed list binder preserves the checked splice"
      true (Expr.equal (reduce (scoped (Some ListType))) Expr.true_);
    let visitor=object inherit [_] Visitors.endo
      method! visit_LVar () _ name=Expr.PVar name end in
    List.iter(fun (ns,vs,n) ->
      let store=Engine.CExprEval.CStore.init
        ["#splice_names",Literal.LList(List.map(fun s -> literal s) ns);
         "#splice_values",Literal.LList(List.map(fun x -> Literal.Num x) vs);
         "#splice_number",Literal.Num n;"#splice_value",Literal.Bool true] in
      let evaluate e=Engine.CExprEval.evaluate_expr store(visitor#visit_expr () e) in
      List.iter(fun term ->
        Alcotest.(check bool) "concrete checked splices preserve payload identity/order"
          true (Literal.equal(evaluate term)(evaluate(reduce term))))
        [insert keys key;insert values descriptor])
      [[],[],0.; [[48]],[nan],1.; [[48];[49]],[-0.;0.],2.])

let checked_prefix_lookup () =
  with_total (fun () ->
    let names=Expr.LVar "#lookup_names" and payload=Expr.LVar "#lookup_values" in
    let number=Expr.LVar "#lookup_length" in
    let gamma ()=let g=Gamma.init () in
      Gamma.update g "#lookup_names" ListType;
      Gamma.update g "#lookup_values" ListType;
      Gamma.update g "#lookup_length" NumberType;g in
    let len e=Expr.UnOp(LstLen,e) in
    let text s=Expr.Lit(Literal.Utf16String(Codec.of_canonical s)) in
    let descriptor=Expr.EList[text "d";number;Expr.true_;Expr.false_;Expr.false_] in
    let whole=Expr.NOp(LstCat,[payload;Expr.EList[descriptor]]) in
    let index=len names in
    let term=bin LstNth (bin LstNth whole index) (Expr.int 1) in
    let fact=eq (len names) (len payload) in
    let context facts=let p=Gillian.Symbolic.Pure_context.init () in
      List.iter(Gillian.Symbolic.Pure_context.extend p) facts;p in
    let reduce ?(g=gamma ()) ?(facts=[fact]) e=
      Reduction.reduce_lexpr ~gamma:g ~pfs:(context facts) e in
    Alcotest.(check bool) "checked key count reads the actual terminal length descriptor"
      true (Expr.equal(reduce term) number);
    let rounded=bin FPlus (bin FPlus number (Expr.num 0.)) (Expr.num 0.) in
    let range=[Expr.UnOp(IsInt,number);bin FLessThanEqual (Expr.num 0.) number;
      bin FLessThan number (Expr.num 4294967295.)] in
    Alcotest.(check bool) "the original writer length-branch query is UNSAT"
      false (Solver.check_satisfiability (bin FLessThan rounded term::fact::range)
        (gamma ()));
    Alcotest.(check bool) "omitting the separate count equality retains the lookup"
      false (Expr.equal(reduce ~facts:[] term) number);
    List.iter(fun x ->let g=gamma () in Gamma.remove g x;
      Alcotest.(check bool) "boundary lookup requires every original list/value type"
        true (try not(Expr.equal(reduce ~g term) number)
          with Reduction.ReductionException _ -> true))
      ["#lookup_names";"#lookup_values";"#lookup_length"];
    let tail=Expr.NOp(LstCat,[payload;Expr.EList[Expr.true_;Expr.false_;number]]) in
    List.iteri(fun offset expected ->
      Alcotest.(check bool) "each in-range literal tail offset has the exact value"
        true (Expr.equal(reduce (bin LstNth tail
          (bin IPlus (Expr.int offset) index))) expected))
      [Expr.true_;Expr.false_;number];
    List.iter(fun offset ->
      Alcotest.(check bool) "negative and out-of-tail offsets cannot read a tail value"
        true (try not(Expr.equal(reduce (bin LstNth whole
          (bin IPlus index (Expr.int offset)))) descriptor)
          with Reduction.ReductionException _ -> true)) [-1;1;2];
    let failure=bin LstNth (Expr.EList []) (Expr.int 0) in
    let unsafe=Expr.NOp(LstCat,[payload;Expr.EList[descriptor;failure]]) in
    Alcotest.(check bool) "a valid selected element cannot conceal a failing later value"
      true (try ignore(reduce (bin LstNth unsafe index));false
       with Reduction.ReductionException _ -> true);
    let store=Engine.CExprEval.CStore.init [] in
    let nan_value=Expr.num nan in
    Alcotest.(check bool) "value identity keeps NaN without assuming numeric reflexivity"
      true (Literal.equal (Engine.CExprEval.evaluate_expr store
          (bin Equal nan_value nan_value)) (Literal.Bool false) &&
        Literal.equal (Engine.CExprEval.evaluate_expr store
          (bin ValueEqual nan_value nan_value)) (Literal.Bool true));
    let scoped ty=Expr.ForAll(["#lookup_names",ty],bin Impl fact (bin ValueEqual term number)) in
    Alcotest.(check bool) "an untyped shadow cannot borrow the outer key-count type"
      false (Expr.equal(reduce (scoped None)) Expr.true_);
    Alcotest.(check bool) "a declared List binder permits the checked boundary read"
      true (Expr.equal(reduce (scoped (Some ListType))) Expr.true_);
    let visitor=object inherit [_] Visitors.endo
      method! visit_LVar () _ name=Expr.PVar name end in
    List.iter(fun (ns,vs,n) ->
      let store=Engine.CExprEval.CStore.init
        ["#lookup_names",Literal.LList(List.map(fun s -> literal s) ns);
         "#lookup_values",Literal.LList(List.map(fun x -> Literal.Num x) vs);
         "#lookup_length",Literal.Num n] in
      let evaluate e=Engine.CExprEval.evaluate_expr store(visitor#visit_expr () e) in
      Alcotest.(check bool) "concrete lookup preserves distinct payload and signed zeros"
        true (Literal.equal(evaluate term)(evaluate(reduce term))))
      [[],[],0.; [],[],nan; [[48]],[nan],-0.; [[48];[49]],[-0.;0.],2.])

let checked_cons_insertion () =
  with_total (fun () ->
    let xs=Expr.LVar "#cons_xs" and head=Expr.LVar "#cons_head" in
    let tail=Expr.LVar "#cons_tail" and i=Expr.LVar "#cons_index" in
    let value=Expr.LVar "#cons_value" in
    let gamma ()=let g=Gamma.init () in
      List.iter(fun x -> Gamma.update g x ListType)
        ["#cons_xs";"#cons_head";"#cons_tail";"#cons_value"];
      Gamma.update g "#cons_index" IntType;g in
    let cons=Expr.NOp(LstCat,[Expr.EList [head];tail]) in
    let len e=Expr.UnOp(LstLen,e) in
    let lower=bin ILessThanEqual (Expr.int 0) i in
    let nonzero=not_(eq i (Expr.int 0)) in
    let upper=bin ILessThanEqual i (bin IPlus (Expr.int 1) (len tail)) in
    let link=eq xs cons in
    let facts=[link;lower;nonzero;upper] in
    let context facts=let p=Gillian.Symbolic.Pure_context.init () in
      List.iter(Gillian.Symbolic.Pure_context.extend p) facts;p in
    let term=Expr.NOp(LstInsert,[xs;i;value]) in
    let wanted=Expr.NOp(LstCat,[Expr.EList [head];
      Expr.NOp(LstInsert,[tail;bin IMinus i (Expr.int 1);value])]) in
    let reduce ?(g=gamma ()) ?(facts=facts) e=
      Reduction.reduce_lexpr ~gamma:(Gamma.copy g) ~pfs:(context facts) e in
    Alcotest.(check bool) "positive integer insertion follows the owned cons witness"
      true (Expr.equal(reduce term)(reduce wanted));
    List.iter(fun positivity ->
      let fs=[link;positivity;upper] in
      Alcotest.(check bool) "either explicit strict-positive integer form is sufficient"
        true (Expr.equal(reduce ~facts:fs term)(reduce ~facts:fs wanted)))
      [bin ILessThan (Expr.int 0) i;bin ILessThanEqual (Expr.int 1) i];
    let original_upper=bin ILessThanEqual i (len xs) in
    let fs=[link;lower;nonzero;original_upper] in
    Alcotest.(check bool) "the original list bound is sufficient without a length alias"
      true (Expr.equal(reduce ~facts:fs term)(reduce ~facts:fs wanted));
    List.iteri(fun omitted _ ->
      Alcotest.(check bool) "every cons/positivity/bound premise is required"
        true (match reduce ~facts:(List.filteri(fun n _ -> n<>omitted) facts) term with
          Expr.NOp(LstInsert,_) -> true | _ -> false)) facts;
    List.iter(fun name ->let g=gamma () in Gamma.remove g name;
      Alcotest.(check bool) "each original list and integer type is required"
        true (try not(Expr.equal(reduce ~g term)(reduce ~g wanted))
          with Reduction.ReductionException _ -> true))
      ["#cons_xs";"#cons_head";"#cons_tail";"#cons_value";"#cons_index"];
    let partial=bin LstNth (Expr.EList []) (Expr.int 0) in
    List.iter(fun unsafe ->
      Alcotest.(check bool) "partial insertion operands still fail before equality erasure"
        true (try ignore(reduce unsafe);false
          with Reduction.ReductionException _ -> true))
      [Expr.NOp(LstInsert,[xs;partial;value]);
       Expr.NOp(LstInsert,[xs;i;partial]);
       Expr.NOp(LstInsert,[Expr.NOp(LstCat,[Expr.EList [head];partial]);i;value])];
    let scoped ty=Expr.ForAll(["#cons_tail",ty],
      List.fold_right(fun f body ->bin Impl f body) facts (eq term wanted)) in
    Alcotest.(check bool) "a shadowed untyped list cannot borrow outer typing"
      false (Expr.equal(reduce(scoped None)) Expr.true_);
    let visitor=object inherit [_] Visitors.endo
      method! visit_LVar () _ name=Expr.PVar name end in
    let atom x=Literal.LList [x] in
    let atoms=[Literal.Num(-0.);Literal.Num 0.;Literal.Num nan;
      Literal.Null;literal [0xd800];Literal.Bool true;Literal.LList []] in
    let checks=ref 0 in
    List.iter(fun v ->List.iter(fun size ->
      let values=List.init size(fun n ->atom(List.nth atoms (n mod List.length atoms))) in
      for index=1 to size+1 do
        let store=Engine.CExprEval.CStore.init [
          "#cons_head",atom(Literal.Num(-0.));"#cons_tail",Literal.LList values;
          "#cons_xs",Literal.LList(atom(Literal.Num(-0.))::values);
          "#cons_index",Literal.Int(Z.of_int index);"#cons_value",atom v] in
        let eval e=Engine.CExprEval.evaluate_expr store(visitor#visit_expr () e) in
        Alcotest.(check bool) "native insertion preserves exact nested values and order"
          true (Literal.equal(eval term)(eval(reduce term)));incr checks
      done) [0;1;2;4]) atoms;
    Alcotest.(check int) "all boundary/value concrete comparisons executed" 77 !checks;
    let small=List.map(fun fs -> Expr.Set.of_list fs)
      [[eq i (Expr.int 0)];[eq i (Expr.int (-1))];
       [eq i (bin IPlus (len tail) (Expr.int 2))]] in
    List.iter(fun fs ->
      let cases=Expr.Set.elements fs @ [eq tail (Expr.EList []);link] in
      Alcotest.(check bool) "omitted positivity or upper bound admits a native countermodel"
        true (Option.is_some(Smt.check_sat(Expr.Set.of_list cases)(Gamma.as_hashtbl(gamma ()))))
    ) small;
    Printf.printf "CHECKED_CONS_INSERTION_CONTROLS_COMPLETE\n%!"
  )

let utf16_list_insertion () =
  with_total (fun () ->
    let xs=Expr.LVar "#insert_keys" and key=Expr.LVar "#insert_key" in
    let pos=Expr.LVar "#insert_position" in
    let gamma ()=let g=Gamma.init () in
      Gamma.update g "#insert_keys" ListType;
      Gamma.update g "#insert_key" Utf16Type;
      Gamma.update g "#insert_position" IntType;g in
    let all e=Expr.UnOp(LstAllUtf16,e) and len e=Expr.UnOp(LstLen,e) in
    let insert xs p k=Expr.NOp(LstInsert,[xs;p;k]) in
    let lower=bin ILessThanEqual Expr.zero_i pos in
    let upper=bin ILessThanEqual pos (len xs) in
    let facts=[lower;upper] in
    let context fs=let p=Gillian.Symbolic.Pure_context.init () in
      List.iter(Gillian.Symbolic.Pure_context.extend p) fs;p in
    let reduce ?(g=gamma ()) ?(facts=facts) e=
      Reduction.reduce_lexpr ~gamma:(Gamma.copy g) ~pfs:(context facts) e in
    let term=all(insert xs pos key) in
    Alcotest.(check bool) "in-range UTF16 insertion preserves exactly the old predicate"
      true (Expr.equal(reduce term)(all xs));
    Alcotest.(check bool) "the abstract insertion typing obligation is UNSAT"
      false (Solver.check_satisfiability (all xs::not_ term::facts) (gamma ()));
    List.iter(fun p ->
      Alcotest.(check bool) "zero and exact list length need no invented bounds"
        true (Expr.equal(reduce ~facts:[] (all(insert xs p key)))(all xs)))
      [Expr.zero_i;len xs];
    let scan=bin KeyInsertIndex xs key in
    Alcotest.(check bool) "typed key insertion uses its checked total domain"
      true (Expr.equal(reduce ~facts:[all xs] (all(insert xs scan key)))(all xs));
    Alcotest.(check bool) "the actual key-scan insertion typing obligation is UNSAT"
      false (Solver.check_satisfiability [all xs;not_(all(insert xs scan key))]
        (gamma ()));
    let retains e=let seen=ref false in
      let visitor=object inherit [_] Visitors.iter as super
        method! visit_expr () e=
          (match e with Expr.UnOp(LstAllUtf16,Expr.NOp(LstInsert,_)) -> seen:=true
           | _ -> ());super#visit_expr () e end in
      visitor#visit_expr () e;!seen in
    List.iteri(fun omitted _ ->
      Alcotest.(check bool) "each explicit insertion bound is required"
        true (retains(reduce ~facts:(List.filteri(fun i _ -> i<>omitted) facts) term))) facts;
    List.iter(fun name ->let g=gamma () in Gamma.remove g name;
      Alcotest.(check bool) "all original operand types are required"
        true (try retains(reduce ~g term)
          with Reduction.ReductionException _ -> true))
      ["#insert_keys";"#insert_key";"#insert_position"];
    Alcotest.(check bool) "key scan cannot borrow missing UTF16 list contents"
      true (retains(reduce ~facts:[] (all(insert xs scan key))));
    Alcotest.(check bool) "wrong inserted type is retained for ordinary evaluation"
      true (retains(reduce (all(insert xs pos (Expr.num 1.)))));
    List.iter(fun p ->
      Alcotest.(check bool) "negative and oversized literal positions retain rejection"
        true (retains(reduce ~facts:[] (all(insert xs p key)))))
      [Expr.int (-1);Expr.int 999];
    let partial=bin LstNth (Expr.EList []) Expr.zero_i in
    List.iter(fun e ->
      Alcotest.(check bool) "partial operands cannot be erased by list typing"
        true (try ignore(reduce ~facts:[] e);false
          with Reduction.ReductionException _ -> true))
      [all(insert partial Expr.zero_i key);all(insert xs partial key);
       all(insert xs Expr.zero_i partial)];
    let scoped ty=Expr.ForAll(["#insert_keys",ty],
      List.fold_right(fun fact body ->bin Impl fact body) facts (eq term (all xs))) in
    Alcotest.(check bool) "an untyped list shadow cannot borrow the outer type"
      false (try Expr.equal(reduce(scoped None)) Expr.true_
        with Reduction.ReductionException _ -> false);
    let visitor=object inherit [_] Visitors.endo
      method! visit_LVar () _ name=Expr.PVar name end in
    let cases=[[];[literal []];[literal [0xd800];literal [65]];
      [Literal.Num(-0.);literal [0xdfff]];[Literal.Null;Literal.Bool true]] in
    let checks=ref 0 in
    List.iter(fun items ->List.iter(fun units ->
      for position=0 to List.length items do
        let store=Engine.CExprEval.CStore.init [
          "#insert_keys",Literal.LList items;"#insert_key",literal units;
          "#insert_position",Literal.Int(Z.of_int position)] in
        let eval e=Engine.CExprEval.evaluate_expr store(visitor#visit_expr () e) in
        Alcotest.(check bool) "native boundary insertion preserves true and false typing"
          true (Literal.equal(eval term)(eval(reduce term)));incr checks
      done) values) cases;
    Alcotest.(check int) "all concrete insertion comparisons executed" 84 !checks;
    Printf.printf "UTF16_INSERTION_DOMAIN_CONTROLS_COMPLETE\n%!"
  )

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
    ("exact Uint32 decimal literals", `Quick, uint32_formatter_literals);
    ("symbolic Uint32 index spelling", `Quick, uint32_formatter_indices);
    ("Uint32 formatter fallback guards", `Quick, uint32_formatter_fallback);
    ("insertion terminal bound", `Quick, insertion_terminal_bound);
    ("insertion complete array width", `Quick, insertion_array_width);
    ("guarded insertion terminal reduction", `Quick, insertion_terminal_reduction);
    ("exact Uint32 integer successor", `Quick, uint32_integer_successor);
    ("dense canonical index scan step", `Quick, dense_index_step);
    ("Uint32 count bounds and fallback", `Quick, uint32_count_bounds);
    ("equal Number integer-count aliases", `Quick, integer_count_alias);
    ("guarded UTF16 list concatenation", `Quick, utf16_list_concatenation);
    ("checked prefix insertion splice", `Quick, checked_prefix_splice);
    ("checked prefix boundary lookup", `Quick, checked_prefix_lookup);
    ("checked cons insertion", `Quick, checked_cons_insertion);
    ("guarded UTF16 list insertion", `Quick, utf16_list_insertion);
  ]
