open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Reduction = Gillian.Logic.Reduction

let n = Expr.num
let x = Expr.LVar "#numeric_x"
let y = Expr.LVar "#numeric_y"
let bin op a b = Expr.BinOp (a, op, b)
let eq = bin Equal
let neg a = Expr.UnOp (Not, a)

let gamma () =
  let gamma = Gamma.init () in
  Gamma.update gamma "#numeric_x" NumberType;
  Gamma.update gamma "#numeric_y" NumberType;
  gamma

let check_sat label expected fs =
  let gamma = gamma () in
  Alcotest.(check bool)
    (label ^ " (SMT)") expected
    (Smt.is_sat (Expr.Set.of_list fs) (Gamma.as_hashtbl gamma));
  Alcotest.(check bool)
    (label ^ " (simplifier + SMT)")
    expected
    (Solver.check_satisfiability fs gamma)

let rounding () =
  let base = 9007199254740992. in
  let range =
    [ bin FLessThanEqual (n base) x; bin FLessThanEqual x (n (base +. 2.)) ]
  in
  let increment = bin FPlus x (n 1.) in
  check_sat "monotonicity has a counterexample" true
    (neg (bin FLessThan x increment) :: range);
  check_sat "monotonicity also has a satisfying input" true
    (bin FLessThan x increment :: range);
  check_sat "exact rounding" false [ eq x (n base); neg (eq increment x) ];
  check_sat "adding two increases every input in this range" false
    (neg (bin FLessThan x (bin FPlus x (n 2.))) :: range)

let special_values () =
  check_sat "NaN is not reflexive" true [ neg (eq x x) ];
  check_sat "NaN can fail both ordered comparisons" true
    [ neg (bin FLessThan x (n 0.)); neg (bin FLessThanEqual (n 0.) x) ];
  check_sat "numeric equality allows either sign of zero" true
    [ eq x (n 0.); eq (bin FDiv (n 1.) x) (n neg_infinity) ];
  check_sat "overflow" false
    [ eq x (n max_float); neg (eq (bin FTimes x (n 2.)) (n infinity)) ];
  check_sat "underflow" false
    [ eq x (n 5e-324); neg (eq (bin FDiv x (n 2.)) (n 0.)) ]

let untyped_equality () =
  let constraints = [ neg (eq x x) ] in
  Alcotest.(check bool)
    "untyped NaN remains possible" true
    (Solver.check_satisfiability constraints (Gamma.init ()));
  (* The same formula has different results under different typings. *)
  let ints = Hashtbl.create 1 in
  Hashtbl.add ints "#numeric_x" Type.IntType;
  let fs = Expr.Set.of_list constraints in
  Alcotest.(check bool)
    "integer equality is reflexive" false (Smt.is_sat fs ints);
  Alcotest.(check bool)
    "numeric equality is not reflexive" true
    (Smt.is_sat fs (Gamma.as_hashtbl (gamma ())))

let arithmetic_matrix () =
  (* Direct SMT queries ensure concrete reduction cannot mask an encoding bug.
     The expected results come from the same binary64 operations as CExprEval. *)
  let values =
    [
      0.;
      -0.;
      1.;
      -1.;
      0.1;
      5e-324;
      max_float;
      9007199254740992.;
      infinity;
      neg_infinity;
      nan;
    ]
  in
  let ops =
    [
      (BinOp.FPlus, ( +. )); (FMinus, ( -. )); (FTimes, ( *. )); (FDiv, ( /. ));
    ]
  in
  List.iter
    (fun (op, concrete) ->
      List.iter
        (fun a ->
          List.iter
            (fun b ->
              let expected = concrete a b in
              let result = bin op (n a) (n b) in
              let property =
                if Float.is_nan expected then Expr.UnOp (M_isNaN, result)
                else if expected = 0. then
                  eq (bin FDiv (n 1.) result) (n (1. /. expected))
                else eq result (n expected)
              in
              let label = Printf.sprintf "%g %s %g" a (BinOp.str op) b in
              Alcotest.(check bool)
                label false
                (Smt.is_sat
                   (Expr.Set.singleton (neg property))
                   (Hashtbl.create 0)))
            values)
        values)
    ops

let reductions () =
  let check label expr =
    let reduced = Reduction.reduce_lexpr ~gamma:(gamma ()) expr in
    Alcotest.(check bool) label true (Expr.equal expr reduced)
  in
  check "no cancellation" (bin FMinus (bin FPlus x y) y);
  check "no reassociation" (bin FPlus (bin FPlus x (n 1.)) (n 1.));
  check "no distribution through conversion"
    (Expr.UnOp (NumToInt, bin FPlus x y));
  check "no cancellation across rounded integer conversion"
    (Expr.UnOp (NumToInt, Expr.UnOp (IntToNum, Expr.LVar "#integer")));
  check "no floating comparison complement" (neg (bin FLessThan x y));
  Alcotest.(check bool)
    "negate keeps unordered possibility" true
    (Expr.equal (Expr.negate (bin FLessThan x y)) (neg (bin FLessThan x y)));
  Alcotest.(check bool)
    "infix does not cancel" true
    (Expr.equal Expr.Infix.(x +. y -. y) (bin FMinus (bin FPlus x y) y));
  Alcotest.(check bool)
    "infix does not annihilate infinity" true
    (Expr.equal Expr.Infix.(n 0. *. x) (bin FTimes (n 0.) x))

let conversions () =
  let rounded =
    Expr.UnOp (IntToNum, Expr.Lit (Int (Z.of_string "9007199254740993")))
  in
  check_sat "integer conversion rounds" false
    [ neg (eq rounded (n 9007199254740992.)) ];
  let truncated = Expr.UnOp (NumToInt, n (-1.5)) in
  check_sat "negative conversion truncates toward zero" false
    [ neg (eq truncated (Expr.int (-1))) ];
  check_sat "infinity is not an integer" false [ Expr.UnOp (IsInt, n infinity) ];
  List.iter
    (fun operand ->
      Alcotest.check_raises "partial conversion fails closed"
        (Smt.SMT_error
           "SMT encoding: NumToInt requires a finite concrete operand")
        (fun () ->
          ignore
            (Smt.is_sat
               (Expr.Set.singleton
                  (eq (Expr.UnOp (NumToInt, operand)) (Expr.int 0)))
               (Gamma.as_hashtbl (gamma ())))))
    [ x; n nan; n infinity ]

let signed_zero_identity () =
  Alcotest.(check bool)
    "structural equality distinguishes zeros" false
    (Expr.equal (n 0.) (n (-0.)));
  Alcotest.(check int)
    "sets distinguish zeros" 2
    (Expr.Set.cardinal (Expr.Set.of_list [ n 0.; n (-0.) ]));
  let predicate zero = eq (bin FDiv (n 1.) (n zero)) (n infinity) in
  List.iter
    (fun zero ->
      Alcotest.(check bool)
        "cached division keeps sign"
        (1. /. zero > 0.)
        (Smt.is_sat (Expr.Set.singleton (predicate zero)) (Hashtbl.create 0)))
    [ 0.; -0.; 0.; -0. ]

let model () =
  let gamma = gamma () in
  let formulae =
    Expr.Set.of_list
      [
        bin FLessThanEqual (n 9007199254740992.) x;
        bin FLessThanEqual x (n 9007199254740994.);
        neg (bin FLessThan x (bin FPlus x (n 1.)));
      ]
  in
  match Smt.check_sat formulae (Gamma.as_hashtbl gamma) with
  | None -> Alcotest.fail "missing rounding counterexample"
  | Some model -> (
      let lifted = ref None in
      Smt.lift_model model (Gamma.as_hashtbl gamma)
        (fun _ value -> lifted := Some value)
        (Expr.Set.singleton x);
      match !lifted with
      | Some (Expr.Lit (Num value)) ->
          Alcotest.(check bool)
            "counterexample replays in binary64" true
            (value >= 9007199254740992. && value <= 9007199254740994.
            && not (value +. 1. > value))
      | _ -> Alcotest.fail "model did not lift a binary64 value")

let integer_division () =
  let gamma = Hashtbl.create 2 in
  Hashtbl.add gamma "#numeric_x" Type.IntType;
  Hashtbl.add gamma "#numeric_y" Type.IntType;
  let values =
    List.init 15 (fun i -> Z.of_int (i - 7))
    @ [
        Z.of_string "100000000000000000000000000000000000001";
        Z.of_string "-100000000000000000000000000000000000001";
      ]
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          if not (Z.equal b Z.zero) then
            List.iter
              (fun (op, operation) ->
                let result = Expr.Lit (Int (operation a b)) in
                let fs =
                  Expr.Set.of_list
                    [
                      eq x (Expr.Lit (Int a));
                      eq y (Expr.Lit (Int b));
                      neg (eq (bin op x y) result);
                    ]
                in
                Alcotest.(check bool)
                  "SMT agrees with Zarith quotient/remainder" false
                  (Smt.is_sat fs gamma))
              [ (BinOp.IDiv, Z.div); (IMod, Z.rem) ])
        values)
    values;
  let product = bin ITimes x y in
  List.iter
    (fun (a, b) ->
      Alcotest.(check bool)
        "division retains required operations" true
        (Expr.equal Expr.Infix.(a / b) (bin IDiv a b)))
    [ (x, product); (y, product); (product, x); (product, y) ]

let integer_predicate () =
  List.iter
    (fun value ->
      let expected = Float.is_integer value in
      let concrete = Engine.CExprEval.evaluate_unop IsInt (Literal.Num value) in
      Alcotest.(check bool)
        "concrete integer predicate" true
        (Literal.equal concrete (Literal.Bool expected));
      Alcotest.(check bool)
        "SMT integer predicate" expected
        (Smt.is_sat
           (Expr.Set.singleton (Expr.UnOp (IsInt, n value)))
           (Hashtbl.create 0)))
    [
      0.;
      -0.;
      1.;
      -1.;
      0.5;
      -0.5;
      9007199254740992.;
      9223372036854775808.;
      Float.max_float;
      infinity;
      neg_infinity;
      nan;
    ]

let number_text () =
  let text e = Expr.UnOp (ToStringOp, e) in
  let str s = Expr.Lit (Literal.String s) in
  check_sat "equal numbers have equal text, including signed zeros" false
    [ eq x y; neg (eq (text x) (text y)) ];
  List.iter
    (fun (value, expected) ->
      let condition =
        if Float.is_nan value then Expr.UnOp (M_isNaN, x) else eq x (n value)
      in
      check_sat
        ("special number text " ^ expected)
        false
        [ condition; neg (eq (text x) (str expected)) ])
    [
      (0., "0");
      (infinity, "Infinity");
      (neg_infinity, "-Infinity");
      (nan, "NaN");
    ];
  List.iter
    (fun spelling ->
      let expression = eq (text x) (str spelling) in
      let reduced = Reduction.reduce_lexpr ~gamma:(gamma ()) expression in
      List.iter
        (fun value ->
          let formatted =
            Engine.CExprEval.evaluate_unop ToStringOp (Literal.Num value)
          in
          let expected = Literal.equal formatted (Literal.String spelling) in
          Alcotest.(check bool)
            (Printf.sprintf "canonical number text %g / %s" value spelling)
            expected
            (Smt.is_sat
               (Expr.Set.of_list [ eq x (n value); reduced ])
               (Gamma.as_hashtbl (gamma ()))))
        [ 0.; -0.; 1.; -1.; 0.5; 1e20; 1e21 ])
    [
      "";
      "0";
      "-0";
      "00";
      "01";
      "+1";
      "1";
      "1.0";
      "1e0";
      "-1";
      "0.5";
      "100000000000000000000";
      "1e+21";
    ];
  List.iter
    (fun spelling ->
      Alcotest.(check bool)
        ("possible property key " ^ spelling)
        true
        (not
           (Expr.equal (Expr.ESet [])
              (Reduction.reduce_lexpr ~gamma:(gamma ())
                 (Expr.NOp
                    ( SetInter,
                      [ Expr.ESet [ text x ]; Expr.ESet [ str spelling ] ] ))))))
    [ "0"; "1"; "-1"; "NaN"; "Infinity" ]

let integer_wraps () =
  let values =
    [
      0.;
      -0.;
      0.5;
      -0.5;
      1.5;
      -1.5;
      65535.;
      65536.;
      -65536.;
      2147483647.;
      2147483648.;
      4294967295.;
      4294967296.;
      -4294967296.;
      9007199254740991.;
      9007199254740992.;
      Float.ldexp 1. 68;
      Float.ldexp 1. 84;
      Float.pred (Float.ldexp 1. 84);
      Float.max_float;
      -.Float.max_float;
      infinity;
      neg_infinity;
      nan;
    ]
  in
  List.iter
    (fun (op, width, signed) ->
      List.iter
        (fun value ->
          let modulus = Z.shift_left Z.one width in
          let wrapped =
            if Float.is_finite value then Z.erem (Z.of_float value) modulus
            else Z.zero
          in
          let expected =
            if signed && Z.geq wrapped (Z.shift_right modulus 1) then
              Z.to_float (Z.sub wrapped modulus)
            else Z.to_float wrapped
          in
          let concrete =
            Engine.CExprEval.evaluate_unop op (Literal.Num value)
          in
          Alcotest.(check bool)
            (Printf.sprintf "%s %g concrete" (UnOp.str op) value)
            true
            (Literal.equal concrete (Literal.Num expected));
          let result = Expr.UnOp (op, n value) in
          let property =
            if expected = 0. then eq (bin FDiv (n 1.) result) (n infinity)
            else eq result (n expected)
          in
          Alcotest.(check bool)
            (Printf.sprintf "%s %g SMT" (UnOp.str op) value)
            false
            (Smt.is_sat (Expr.Set.singleton (neg property)) (Hashtbl.create 0)))
        values)
    [
      (UnOp.ToUint32Op, 32, false);
      (ToUint16Op, 16, false);
      (ToInt32Op, 32, true);
    ];
  List.iter
    (fun op ->
      check_sat "integer wrap canonicalizes both zeros" false
        [
          eq x (n 0.);
          neg (eq (bin FDiv (n 1.) (Expr.UnOp (op, x))) (n infinity));
        ])
    [ UnOp.ToUint32Op; ToUint16Op; ToInt32Op ]

let integer_truncation () =
  let values =
    [
      0.;
      -0.;
      0.5;
      -0.5;
      1.5;
      -1.5;
      4294967295.;
      9007199254740991.;
      Float.max_float;
      -.Float.max_float;
      infinity;
      neg_infinity;
      nan;
    ]
  in
  List.iter
    (fun value ->
      let expected = if Float.is_nan value then 0. else Float.trunc value in
      let output = Engine.CExprEval.evaluate_unop ToIntOp (Literal.Num value) in
      Alcotest.(check bool)
        "ToInteger concrete" true
        (Literal.equal output (Literal.Num expected));
      let result = Expr.UnOp (ToIntOp, n value) in
      let property =
        if expected = 0. then eq (bin FDiv (n 1.) result) (n (1. /. expected))
        else eq result (n expected)
      in
      Alcotest.(check bool)
        "ToInteger SMT" false
        (Smt.is_sat (Expr.Set.singleton (neg property)) (Hashtbl.create 0)))
    values;
  check_sat "integral values survive truncation" false
    [ Expr.UnOp (IsInt, x); neg (eq (Expr.UnOp (ToIntOp, x)) x) ]

let integer_truncation_predicate () =
  let predicate e = Expr.UnOp (IsInt, Expr.UnOp (ToIntOp, e)) in
  let expected = neg (bin Or (eq x (n infinity)) (eq x (n neg_infinity))) in
  check_sat "only infinities retain a non-integral ToInteger result" false
    [ neg (eq (predicate x) expected) ];
  check_sat "NaN is admitted and truncates to an integer" true
    [ neg (eq x x); predicate x ];
  check_sat "a non-integral ToInteger result remains possible" true
    [ neg (predicate x) ];
  List.iter
    (fun value ->
      let result = Engine.CExprEval.evaluate_unop ToIntOp (Literal.Num value) in
      let expected =
        match Engine.CExprEval.evaluate_unop IsInt result with
        | Literal.Bool b -> b
        | _ -> assert false
      in
      check_sat "typed composite agrees with executable operations" false
        [
          bin ValueEqual x (n value);
          neg (eq (predicate x) (Expr.bool expected));
        ];
      Alcotest.(check bool)
        "wrapped Number keeps the same composite predicate" false
        (Smt.is_sat
           (Expr.Set.of_list
              [
                bin ValueEqual x (n value);
                neg (eq (predicate x) (Expr.bool expected));
              ])
           (Hashtbl.create 0)))
    [
      0.;
      -0.;
      0.5;
      -0.5;
      1.5;
      -1.5;
      5e-324;
      -5e-324;
      9007199254740991.;
      9007199254740992.;
      max_float;
      -.max_float;
      infinity;
      neg_infinity;
      nan;
    ];
  List.iter
    (fun value ->
      Alcotest.(check bool)
        "composite keeps the wrapped Number type guard" false
        (Smt.is_sat
           (Expr.Set.of_list [ bin ValueEqual x value; predicate x ])
           (Hashtbl.create 0)))
    [
      Expr.Lit Literal.Undefined;
      Expr.Lit Literal.Null;
      Expr.bool true;
      Expr.int 0;
      Expr.Lit (Literal.String "0");
      Expr.EList [];
    ]

let formatter_roundtrip () =
  let result =
    Reduction.reduce_lexpr ~gamma:(gamma ())
      (Expr.UnOp (ToNumberOp, Expr.UnOp (ToStringOp, x)))
  in
  check_sat "formatter-produced text recovers non-NaN numbers" false
    [ eq x x; neg (eq result x) ];
  check_sat "formatter roundtrip canonicalizes zero" false
    [ eq x (n 0.); neg (eq (bin FDiv (n 1.) result) (n infinity)) ];
  check_sat "formatter roundtrip does not preserve negative zero" true
    [ eq x (n 0.); neg (eq (bin FDiv (n 1.) result) (bin FDiv (n 1.) x)) ];
  check_sat "formatter roundtrip preserves NaN" false
    [ neg (eq x x); eq result result ]

let symbolic_indices () =
  let old_total = !Gillian.Utils.Config.Verification.total in
  Gillian.Utils.Config.Verification.total := true;
  Fun.protect
    ~finally:(fun () -> Gillian.Utils.Config.Verification.total := old_total)
    (fun () ->
      let index = Expr.UnOp (NumToInt, x) in
      let bounds =
        [
          bin FLessThanEqual (n 0.) x;
          bin FLessThanEqual x (n 1.);
          Expr.UnOp (IsInt, x);
        ]
      in
      check_sat "symbolic index bounds" false
        (neg
           (bin And
              (bin ILessThanEqual (Expr.int 0) index)
              (bin ILessThanEqual index (Expr.int 1)))
        :: bounds);
      check_sat "symbolic zero index" false
        (bin FLessThan x (n 1.) :: neg (eq index (Expr.int 0)) :: bounds);
      check_sat "symbolic one index" false
        (neg (bin FLessThan x (n 1.)) :: neg (eq index (Expr.int 1)) :: bounds);
      check_sat "symbolic negative conversion truncates" false
        [
          bin FLessThan (n (-2.)) x;
          bin FLessThan x (n (-1.));
          neg (eq index (Expr.int (-1)));
        ])

let runtime_constants () =
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun constant ->
      let source = Expr.Lit (Literal.Constant constant) in
      let concrete = Engine.CExprEval.evaluate_expr store source in
      let property = eq source (Expr.Lit concrete) in
      Alcotest.(check bool)
        "fixed constant agrees with concrete evaluator" true
        (Expr.equal (Reduction.reduce_lexpr property) Expr.true_);
      check_sat "fixed constant SMT" false [ neg property ])
    [ Constant.Min_float; Max_float; MaxSafeInteger; Epsilon; Pi ];
  List.iter
    (fun constant ->
      Alcotest.(check bool)
        "dynamic constant is not sampled in simplification" true
        (Option.is_none (Literal.static_constant constant)))
    [ Constant.Random; UTCTime; LocalTime ];
  let random_state = Random.get_state () in
  Fun.protect
    ~finally:(fun () -> Random.set_state random_state)
    (fun () ->
      Random.init 42;
      let draw = Expr.Lit (Literal.Constant Constant.Random) in
      Alcotest.(check bool)
        "identical syntax does not identify separate random draws" true
        (Literal.equal
           (Engine.CExprEval.evaluate_expr store (eq draw draw))
           (Literal.Bool false)))

let numeric_strings () =
  let open Yojson.Basic.Util in
  let cases =
    Yojson.Basic.from_file "numeric_strings.json" |> member "values" |> to_list
  in
  let check label expected = function
    | Literal.Num actual ->
        if Float.is_nan expected then
          Alcotest.(check bool) label true (Float.is_nan actual)
        else
          Alcotest.(check int64)
            label
            (Int64.bits_of_float expected)
            (Int64.bits_of_float actual)
    | _ -> Alcotest.fail (label ^ ": expected a number")
  in
  List.iteri
    (fun index case ->
      let units = case |> member "units" |> to_list |> List.map to_int in
      let string = Gillian.Utils.Utf16.of_code_units units in
      let expected =
        case |> member "expectedBits" |> to_string
        |> (fun s -> Int64.of_string ("0x" ^ s))
        |> Int64.float_of_bits
      in
      let input = Literal.String string in
      check
        (Printf.sprintf "numeric string %d concrete" index)
        expected
        (Engine.CExprEval.evaluate_unop ToNumberOp input);
      match Reduction.reduce_lexpr (Expr.UnOp (ToNumberOp, Expr.Lit input)) with
      | Expr.Lit output ->
          check
            (Printf.sprintf "numeric string %d reduction" index)
            expected output
      | _ -> Alcotest.fail "numeric string did not reduce")
    cases

let formatter_keys () =
  let text e = Expr.UnOp (ToStringOp, e) in
  let parse e = Expr.UnOp (ToNumberOp, e) in
  let isnan e = Expr.UnOp (M_isNaN, e) in
  let same = bin Or (eq x y) (bin And (isnan x) (isnan y)) in
  check_sat "ordered numeric keys cannot collide" false
    [ bin FLessThan x y; eq (text x) (text y) ];
  check_sat "equal text identifies numbers modulo zero and NaN" false
    [ eq (text x) (text y); neg same ];
  check_sat "NaN key differs from a finite key" false
    [ isnan x; eq y (n 1.); eq (text x) (text y) ];
  check_sat "equal finite keys remain possible" true
    [ eq x (n 1.); eq y (n 1.); eq (text x) (text y) ];
  check_sat "different finite keys remain possible" true
    [ eq x (n 1.); eq y (n 2.); neg (eq (text x) (text y)) ];
  let inverse = bin Or (isnan x) (eq (parse (text x)) x) in
  let all body = Expr.ForAll ([ ("#numeric_x", Some Type.NumberType) ], body) in
  let some body =
    Expr.Exists ([ ("#numeric_x", Some Type.NumberType) ], body)
  in
  check_sat "formatter facts stay inside universal scope" false
    [ neg (all inverse) ];
  check_sat "formatter facts stay inside existential scope" false
    [ some (neg inverse) ];
  check_sat "a false universal formatter claim has a witness" true
    [ neg (all (eq (parse (text x)) (n 0.))) ]

let value_identity () =
  let same = bin ValueEqual in
  let box e = Expr.EList [ e ] in
  check_sat "value identity distinguishes signed zero" false
    [ same (n 0.) (n (-0.)) ];
  check_sat "value identity is reflexive at NaN" false
    [ neg (same (n nan) (n nan)) ];
  check_sat "symbolic value identity is reflexive" false [ neg (same x x) ];
  check_sat "numeric equality does not imply value identity" true
    [ eq x (n 0.); neg (same x (n 0.)) ];
  check_sat "list equality preserves signed zero" false
    [ eq (box (n 0.)) (box (n (-0.))) ];
  check_sat "list equality preserves NaN" false
    [ neg (eq (box (n nan)) (box (n nan))) ];
  let items = Expr.LVar "#identity_items" in
  let head = bin LstNth items (Expr.int 0) in
  check_sat "numeric head comparison cannot substitute its zero sign" true
    [
      eq (Expr.UnOp (LstLen, items)) (Expr.int 1);
      eq head (n 0.);
      same head (n (-0.));
    ];
  let store = Engine.CExprEval.CStore.init [] in
  List.iter
    (fun (source, expected) ->
      let value = Engine.CExprEval.evaluate_expr store source in
      Alcotest.(check bool)
        "concrete identity agrees" true
        (Literal.equal value (Bool expected));
      let reduced = Reduction.reduce_lexpr source in
      Alcotest.(check bool)
        "reduced identity agrees" true
        (Expr.equal reduced (Expr.bool expected)))
    [
      (same (n 0.) (n (-0.)), false);
      (same (n nan) (n nan), true);
      (eq (n 0.) (n (-0.)), true);
      (eq (n nan) (n nan), false);
      (eq (box (n 0.)) (box (n (-0.))), false);
      (eq (box (n nan)) (box (n nan)), true);
    ]

let list_cons_identity () =
  let left = Expr.LVar "#cons_left" and right = Expr.LVar "#cons_right" in
  let cons head tail = Expr.NOp (LstCat, [ Expr.EList [ n head ]; tail ]) in
  List.iter
    (fun (a, b, expected) ->
      let source = eq (cons a left) (cons b right) in
      let reduced = Reduction.reduce_lexpr source in
      let tails = [ eq left (Expr.EList []); eq right (Expr.EList []) ] in
      check_sat "cons equality before reduction" false
        (neg (eq source (Expr.bool expected)) :: tails);
      check_sat "cons equality after reduction" false
        (neg (eq reduced (Expr.bool expected)) :: tails);
      let literal =
        Expr.BinOp (Expr.EList [ n a ], Equal, Expr.EList [ n b ])
      in
      let actual =
        Engine.CExprEval.evaluate_expr (Engine.CExprEval.CStore.init []) literal
      in
      Alcotest.(check bool)
        "cons agrees with concrete list equality" true
        (Literal.equal actual (Bool expected)))
    [ (-0., 0., false); (nan, nan, true); (1., 1., true); (1., 2., false) ]

let literal_parser_facts () =
  let text = Expr.UnOp (ToStringOp, x) in
  let domain = Expr.ESet [ Expr.Lit (String "push"); text ] in
  let restored = bin SetDiff domain (Expr.ESet [ text ]) in
  let integral =
    [
      Expr.UnOp (IsInt, x);
      bin FLessThanEqual (n 0.) x;
      bin FLessThanEqual x (n 4294967295.);
    ]
  in
  check_sat "formatter literal identity inside sets" false
    (neg (eq restored (Expr.ESet [ Expr.Lit (String "push") ])) :: integral);
  List.iter
    (fun spelling ->
      let literal = Expr.Lit (String spelling) in
      let parsed = Expr.UnOp (ToNumberOp, literal) in
      let expected = Utils.Arith_utils.string_to_number spelling in
      check_sat
        ("literal parser " ^ spelling)
        false
        [ neg (bin ValueEqual parsed (n expected)) ])
    [ "push"; "0"; "-0"; "01"; "0x10"; "Infinity"; "NaN"; " "; "1e3"; "\255" ]

let empty_set_subset () =
  let set = Expr.LVar "#empty_subset_set" in
  let subset = bin SetSub set (Expr.ESet []) in
  let reduced = Reduction.reduce_lexpr subset in
  List.iter
    (fun (elements, expected) ->
      let bound = eq set (Expr.ESet elements) in
      check_sat "raw empty-set subset" false
        [ bound; neg (eq subset (Expr.bool expected)) ];
      check_sat "reduced empty-set subset" false
        [ bound; neg (eq reduced (Expr.bool expected)) ])
    [ ([], true); ([ Expr.Lit (String "x") ], false) ]

let boolean_literal_comparison () =
  let predicate = eq x (n 0.) in
  List.iter
    (fun negate ->
      let expression = if negate then neg predicate else predicate in
      List.iter
        (fun literal ->
          List.iter
            (fun reverse ->
              let comparison =
                if reverse then eq (Expr.bool literal) expression
                else eq expression (Expr.bool literal)
              in
              let reduced =
                Reduction.reduce_lexpr ~gamma:(gamma ()) comparison
              in
              List.iter
                (fun number ->
                  let expected =
                    (if negate then not (number = 0.) else number = 0.)
                    = literal
                  in
                  let binding = bin ValueEqual x (n number) in
                  check_sat "Boolean equality before reduction" false
                    [ binding; neg (eq comparison (Expr.bool expected)) ];
                  check_sat "Boolean equality after reduction" false
                    [ binding; neg (eq reduced (Expr.bool expected)) ])
                [ 0.; -0.; 1.; nan ])
            [ false; true ])
        [ false; true ])
    [ false; true ]

let exact_numeric_aliases () =
  let module P = Gillian.Symbolic.Pure_context in
  let module Subst = Gillian.Symbolic.Subst in
  List.iter
    (fun save ->
      List.iter
        (fun number ->
          let g = gamma () in
          let facts =
            P.of_list [ bin ValueEqual x y; bin ValueEqual y (n number) ]
          in
          let subst, _ =
            Gillian.Logic.Simplifications.simplify_pfs_and_gamma
              ~save_spec_vars:(Utils.Containers.SS.empty, save)
              facts g
          in
          let preserved = P.to_list facts in
          Alcotest.(check bool)
            "alias simplification preserves satisfiability" true
            (Smt.is_sat (Expr.Set.of_list preserved) (Gamma.as_hashtbl g));
          let actual = Subst.subst_in_expr subst ~partial:true x in
          Alcotest.(check bool)
            "substitution preserves exact number identity" false
            (Smt.is_sat
               (Expr.Set.of_list
                  (neg (bin ValueEqual actual (n number)) :: preserved))
               (Gamma.as_hashtbl g));
          if save then
            List.iter
              (fun variable ->
                Alcotest.(check bool)
                  "saved alias retains exact identity" false
                  (Smt.is_sat
                     (Expr.Set.of_list
                        (neg (bin ValueEqual variable (n number)) :: preserved))
                     (Gamma.as_hashtbl g)))
              [ x; y ])
        [ 0.; -0.; nan; infinity; neg_infinity; 1.; max_float ])
    [ false; true ]

let bitwise_and () =
  let values =
    [
      0.;
      -0.;
      0.5;
      -0.5;
      1.;
      -1.;
      55296.;
      56320.;
      57343.;
      64512.;
      65535.;
      2147483647.;
      -2147483648.;
      2147483648.;
      4294967295.;
      4294967297.;
      -4294967297.;
      9007199254740991.;
      Float.max_float;
      infinity;
      neg_infinity;
      nan;
    ]
  in
  let word value =
    if Float.is_finite value then
      Z.erem (Z.of_float value) (Z.shift_left Z.one 32)
    else Z.zero
  in
  List.iter
    (fun a ->
      List.iter
        (fun b ->
          let bits = Z.logand (word a) (word b) in
          let signed =
            if Z.testbit bits 31 then Z.sub bits (Z.shift_left Z.one 32)
            else bits
          in
          let expected = Z.to_float signed in
          let concrete =
            Engine.CExprEval.evaluate_binop
              (Engine.CExprEval.CStore.init [])
              BitwiseAndF (n a) (n b)
          in
          Alcotest.(check bool)
            "Number AND concrete matches modular integer oracle" true
            (Literal.equal concrete (Literal.Num expected));
          let result = bin BitwiseAndF (n a) (n b) in
          let property =
            if expected = 0. then eq (bin FDiv (n 1.) result) (n infinity)
            else eq result (n expected)
          in
          Alcotest.(check bool)
            "Number AND SMT matches modular integer oracle" false
            (Smt.is_sat (Expr.Set.singleton (neg property)) (Hashtbl.create 0)))
        values)
    values;
  let result = bin BitwiseAndF x y in
  check_sat "all Number AND results are integral" false
    [ neg (Expr.UnOp (IsInt, result)) ];
  check_sat "all Number AND results are signed 32-bit" false
    [
      bin Or
        (bin FLessThan result (n (-2147483648.)))
        (bin FLessThan (n 2147483647.) result);
    ];
  let mask = bin BitwiseAndF x (n 64512.) in
  check_sat "arbitrary Number mask admits low surrogate" true
    [ eq mask (n 56320.) ];
  check_sat "arbitrary Number mask admits other values" true
    [ neg (eq mask (n 56320.)) ]

let bitwise_and_models () =
  let previous_dump = !Gillian.Utils.Config.dump_smt in
  Gillian.Utils.Config.dump_smt :=
    Option.is_some (Sys.getenv_opt "GILLIAN_BITWISE_AND_MODELS");
  Fun.protect
    ~finally:(fun () -> Gillian.Utils.Config.dump_smt := previous_dump)
    (fun () ->
      let z = Expr.LVar "#bitand_result" in
      let gamma = Gamma.as_hashtbl (gamma ()) in
      Hashtbl.add gamma "#bitand_result" NumberType;
      let models =
        List.map
          (fun (id, extra) ->
            let constraints = eq z (bin BitwiseAndF x y) :: extra in
            let model =
              match Smt.exec_sat (Expr.Set.of_list constraints) gamma with
              | Some m -> m
              | None -> Alcotest.fail ("Missing AND witness: " ^ id)
            in
            let lifted = Hashtbl.create 3 in
            Smt.lift_model model gamma (Hashtbl.add lifted)
              (Expr.Set.of_list [ x; y; z ]);
            let get name =
              match Hashtbl.find_opt lifted name with
              | Some (Expr.Lit value) -> value
              | _ -> Alcotest.fail "Missing AND model value"
            in
            let store =
              Engine.CExprEval.CStore.init
                (List.map
                   (fun name -> (name, get name))
                   [ "#numeric_x"; "#numeric_y"; "#bitand_result" ])
            in
            let visitor =
              object
                inherit [_] Visitors.endo
                method! visit_LVar () _ name = Expr.PVar name
              end
            in
            List.iter
              (fun e ->
                match
                  Engine.CExprEval.evaluate_expr store (visitor#visit_expr () e)
                with
                | Bool true -> ()
                | _ ->
                    Alcotest.fail "AND witness failed complete concrete replay")
              constraints;
            let bits name =
              match get name with
              | Num n ->
                  `String (Printf.sprintf "%016Lx" (Int64.bits_of_float n))
              | _ -> Alcotest.fail "AND witness lost Number type"
            in
            `Assoc
              [
                ("id", `String id);
                ("leftBits", bits "#numeric_x");
                ("rightBits", bits "#numeric_y");
                ("resultBits", bits "#bitand_result");
              ])
          ([
             ("low-mask", [ eq y (n 64512.); eq z (n 56320.) ]);
             ("other-mask", [ eq y (n 64512.); neg (eq z (n 56320.)) ]);
           ]
          @ List.map
              (fun (id, a, b) ->
                (id, [ bin ValueEqual x (n a); bin ValueEqual y (n b) ]))
              [
                ("negative-result", -1., -1.);
                ("positive-overflow", 4294967297., -1.);
                ("negative-overflow", -4294967297., -1.);
                ("fraction", -1.9, 2147483647.);
                ("nan", nan, -1.);
                ("positive-infinity", infinity, -1.);
                ("negative-infinity", neg_infinity, -1.);
                ("negative-zero", -0., -1.);
                ("subnormal", 5e-324, -1.);
                ("huge", Float.max_float, -1.);
              ])
      in
      match Sys.getenv_opt "GILLIAN_BITWISE_AND_MODELS" with
      | None -> ()
      | Some path -> Yojson.Safe.to_file path (`List models))

let tests =
  [
    ("Number bitwise AND", `Quick, bitwise_and);
    ("Number AND models", `Quick, bitwise_and_models);
    ("rounding", `Quick, rounding);
    ("signed integer division", `Quick, integer_division);
    ("integer predicate parity", `Quick, integer_predicate);
    ("special values", `Quick, special_values);
    ("untyped equality and typed caching", `Quick, untyped_equality);
    ("arithmetic differential matrix", `Quick, arithmetic_matrix);
    ("reductions", `Quick, reductions);
    ("numeric conversions", `Quick, conversions);
    ("number text", `Quick, number_text);
    ("value identity and resource matching", `Quick, value_identity);
    ("list decomposition identity", `Quick, list_cons_identity);
    ("ground literal parser facts", `Quick, literal_parser_facts);
    ("empty-set subset", `Quick, empty_set_subset);
    ("Boolean literal comparisons", `Quick, boolean_literal_comparison);
    ("exact numeric aliases", `Quick, exact_numeric_aliases);
    ("formatter key identities", `Quick, formatter_keys);
    ("integer wrap conversions", `Quick, integer_wraps);
    ("ECMAScript numeric strings", `Quick, numeric_strings);
    ("integer truncation", `Quick, integer_truncation);
    ("integer truncation predicate", `Quick, integer_truncation_predicate);
    ("formatter roundtrip", `Quick, formatter_roundtrip);
    ("symbolic list indices", `Quick, symbolic_indices);
    ("runtime constants", `Quick, runtime_constants);
    ("signed zero identity and caching", `Quick, signed_zero_identity);
    ("counterexample model", `Quick, model);
  ]
