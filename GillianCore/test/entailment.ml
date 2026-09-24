open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Config = Gillian.Utils.Config

let bin op a b = Expr.BinOp (a, op, b)
let not_ e = Expr.UnOp (Not, e)
let x = Expr.LVar "#focus_x"
let y = Expr.LVar "#focus_y"
let z = Expr.LVar "#focus_z"

let with_total f () =
  let saved = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := saved) f

let gamma () =
  let g = Gamma.init () in
  List.iter
    (fun name -> Gamma.update g name Type.IntType)
    [ "#focus_x"; "#focus_y"; "#focus_z" ];
  g

let entails facts goal =
  Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
    [ goal ] (gamma ())

let sufficient () =
  let facts = [ bin ILessThan x (Expr.int 0); bin ILessThan (Expr.int 7) z ] in
  Alcotest.(check bool)
    "irrelevant facts do not prevent a sufficient proof" true
    (entails facts (bin ILessThanEqual x (Expr.int 0)));
  Alcotest.(check bool)
    "a false goal still rejects" false
    (entails facts (bin ILessThan x (Expr.int (-2))))

let fallback () =
  (* A goal-local subset retains x < y but omits y <= 0. It has a model for
     x >= 0, whereas the full conjunction has none. SAT must fall back. *)
  let facts = [ bin ILessThan x y; bin ILessThanEqual y (Expr.int 0) ] in
  Alcotest.(check bool)
    "full query proves after inconclusive subset" true
    (entails facts (bin ILessThan x (Expr.int 0)));
  Alcotest.(check bool)
    "full-query counterexample remains a rejection" false
    (entails facts (bin ILessThan x (Expr.int (-1))))

let finite_position () =
  let s = Expr.LVar "#s" and index = Expr.LVar "#index" in
  let pos = Expr.UnOp (ToIntOp, index) in
  let len = Expr.UnOp (IntToNum, Expr.UnOp (Utf16Len, s)) in
  let fs =
    Expr.Set.of_list
      [
        not_ (Expr.UnOp (IsInt, pos));
        not_ (bin FLessThan pos (Expr.num 0.));
        not_ (bin FLessThanEqual len pos);
      ]
  in
  let g = Gamma.init () in
  Gamma.update g "#s" Type.Utf16Type;
  Gamma.update g "#index" Type.NumberType;
  let g = Gamma.as_hashtbl g in
  (* The same native query has a separate constrained resource-control run:
     SMT_TIMEOUT=1 run_tests.exe test 'Sufficient entailment' 2 --json.
     Default runs must prove it, allowing the required full-budget fallback;
     the short-budget run must remain inconclusive
     and the required-query API must still raise its ordinary totality error. *)
  if Sys.getenv_opt "SMT_TIMEOUT" = Some "1" then (
    Alcotest.(check bool)
      "optional unknown cannot prove UNSAT" false (Smt.proves_unsat fs g);
    let rejected check =
      try
        check ();
        false
      with
      | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
        msg = "Incomplete totality proof: SMT returned unknown"
    in
    Alcotest.(check bool)
      "required unknown remains an error" true
      (rejected (fun () -> ignore (Smt.exec_sat fs g)));
    Hashtbl.add g "#other_s" Type.Utf16Type;
    Hashtbl.add g "#other_index" Type.NumberType;
    let seeded_fs =
      Expr.Set.add
        (bin Equal (Expr.LVar "#other_s") s)
        (Expr.Set.add (bin Equal (Expr.LVar "#other_index") index) fs)
    in
    Alcotest.(check bool)
      "seed failure cannot hide required unknown" true
      (rejected (fun () -> ignore (Smt.is_sat seeded_fs g)));
    Hashtbl.remove g "#other_s";
    Hashtbl.remove g "#other_index";
    Hashtbl.add g "#length" Type.NumberType;
    let single_pair = Expr.Set.add (bin Equal (Expr.LVar "#length") len) fs in
    Alcotest.(check bool)
      "single-pair seed failure cannot hide required unknown" true
      (rejected (fun () -> ignore (Smt.is_sat single_pair g))))
  else
    (* The optional API may legitimately use its bounded unknown outcome.
       A false precheck is not a proof: require actual UNSAT from the original
       query with its full native budget before this control may pass. *)
    let proved = Smt.proves_unsat fs g in
    Alcotest.(check bool)
      "inside ToInteger position is proved by precheck or full query" true
      (proved || Option.is_none (Smt.exec_sat fs g))

let witness_query () =
  let s = Expr.LVar "#witness_s" and i = Expr.LVar "#witness_i" in
  let empty =
    Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical ""))
  in
  let g = Gamma.init () in
  Gamma.update g "#witness_s" Type.Utf16Type;
  Gamma.update g "#witness_i" Type.NumberType;
  Gamma.update g "#witness_other_s" Type.Utf16Type;
  Gamma.update g "#witness_other_i" Type.NumberType;
  let other =
    [
      bin Equal (Expr.LVar "#witness_other_s") empty;
      bin Equal (Expr.LVar "#witness_other_i") (Expr.num 0.);
    ]
  in
  (s, i, empty, g, other)

let seeded_witness () =
  let s, i, empty, g, other = witness_query () in
  let facts =
    [
      bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 0);
      bin Equal i (Expr.num 0.);
    ]
  in
  Alcotest.(check bool)
    "validated full-query witness establishes feasibility" true
    (Smt.is_sat (Expr.Set.of_list (other @ facts)) (Gamma.as_hashtbl g));
  (* A successful witness search must not add its guesses to later proof state. *)
  Alcotest.(check bool)
    "zero index does not force the string to be empty" false
    (Solver.check_entailment Utils.Containers.SS.empty
       (Engine.PFS.of_list [ bin Equal i (Expr.num 0.) ])
       [ bin Equal s empty ]
       g)

let seeded_fallback () =
  let s, i, empty, g, other = witness_query () in
  let different =
    [ not_ (bin Equal s empty); not_ (bin Equal i (Expr.num 0.)) ]
  in
  Alcotest.(check bool)
    "UNSAT seed falls back to a satisfiable full query" true
    (Smt.is_sat (Expr.Set.of_list (other @ different)) (Gamma.as_hashtbl g));
  Alcotest.(check bool)
    "contradictory full query cannot gain a witness" false
    (Smt.is_sat
       (Expr.Set.of_list (other @ (bin Equal s empty :: different)))
       (Gamma.as_hashtbl g))

let single_pair_witness () =
  let s = Expr.LVar "#single_s" and n = Expr.LVar "#single_n" in
  let value = Expr.LVar "#single_value" in
  let size = Expr.UnOp (Utf16Len, s) in
  let g = Gamma.init () in
  Gamma.update g "#single_s" Type.Utf16Type;
  Gamma.update g "#single_n" Type.NumberType;
  (* This is the actual AJV invariant-production query, with one pair and an
     untyped scope value. Every assertion must survive the optional search. *)
  let fs =
    Expr.Set.of_list
      [
        not_ (bin Equal value (Expr.Lit Literal.Nono));
        bin Equal n (Expr.UnOp (IntToNum, size));
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
      ]
  in
  let gamma = Gamma.as_hashtbl g in
  Alcotest.(check bool)
    "one-pair feasibility succeeds" true (Smt.is_sat fs gamma);
  let nonempty =
    Expr.Set.add
      (bin Equal size (Expr.int 1))
      (Expr.Set.add (bin Equal n (Expr.num 1.)) fs)
  in
  let empty =
    Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical ""))
  in
  Alcotest.(check bool)
    "the empty guess contradicts the nonempty query" false
    (Smt.is_sat (Expr.Set.add (bin Equal s empty) nonempty) gamma);
  Alcotest.(check bool)
    "the complete nonempty query succeeds after seed failure" true
    (Smt.is_sat nonempty gamma);
  Alcotest.(check bool)
    "witness guesses do not rule out later nonempty inputs" true
    (Smt.is_sat
       (Expr.Set.add
          (bin Equal size (Expr.int 2))
          (Expr.Set.add (bin Equal n (Expr.num 2.)) fs))
       gamma);
  Alcotest.(check bool)
    "a contradictory full query cannot gain a witness" false
    (Smt.is_sat
       (Expr.Set.add (bin Equal value (Expr.Lit Literal.Nono)) fs)
       gamma)

let length_only_witness () =
  let s = Expr.LVar "#branch_s" and len = Expr.LVar "#branch_len" in
  let pos = Expr.LVar "#branch_pos" and count = Expr.LVar "#branch_count" in
  let rank = Expr.LVar "#branch_rank" in
  let size = Expr.UnOp (Utf16Len, s) in
  let number = Expr.UnOp (IntToNum, size) in
  let maximum = Expr.num 9007199254740991. in
  let g = Gamma.init () in
  Gamma.update g "#branch_s" Type.Utf16Type;
  Gamma.update g "#branch_len" Type.NumberType;
  Gamma.update g "#branch_pos" Type.NumberType;
  (* The actual compiled AJV branch query leaves count and the saved rank
     wrapped/untyped. Its Number equalities must survive witness search. *)
  let common =
    Expr.Set.of_list
      [
        Expr.UnOp (IsInt, count);
        Expr.UnOp (IsInt, len);
        Expr.UnOp (IsInt, pos);
        bin FLessThanEqual (Expr.num 0.) count;
        bin FLessThanEqual count pos;
        bin ValueEqual len number;
        bin Equal len number;
        bin Equal len len;
        bin Equal pos pos;
        bin FLessThanEqual len maximum;
        bin ValueEqual rank (bin FMinus maximum pos);
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
      ]
  in
  let gamma = Gamma.as_hashtbl g in
  let inside = Expr.Set.add (bin FLessThan pos len) common in
  let outside =
    Expr.Set.add
      (bin FLessThanEqual pos len)
      (Expr.Set.add (bin FLessThanEqual len pos) common)
  in
  let check label expected fs =
    Alcotest.(check bool) label expected (Smt.is_sat fs gamma)
  in
  let bare_nonempty =
    Expr.Set.of_list
      [
        bin FLessThan (Expr.num 0.) number;
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
      ]
  in
  check "inlined rounded-length comparison retains nonempty feasibility" true
    bare_nonempty;
  check "bare comparison keeps the complete length contradiction" false
    (Expr.Set.add (bin Equal size (Expr.int 0)) bare_nonempty);
  check "negated reverse comparison also permits a two-unit witness" true
    (Expr.Set.of_list
       [ Expr.UnOp (Not, bin FLessThanEqual number (Expr.num 1.)) ]);
  check "bare comparison fallback still permits longer input" true
    (Expr.Set.add (bin Equal size (Expr.int 3)) bare_nonempty);
  Alcotest.(check bool)
    "model-returning API also finds the complete nonempty witness" true
    (Option.is_some (Smt.check_sat inside gamma));
  check "the other branch remains feasible" true outside;
  check "a length-zero guess cannot satisfy the inside branch" false
    (Expr.Set.add (bin Equal size (Expr.int 0)) inside);
  check "a contradictory count cannot gain a witness" false
    (Expr.Set.add (bin FLessThan count (Expr.num 0.)) inside);
  check "a contradictory rank cannot gain a witness" false
    (Expr.Set.add (bin ValueEqual rank (Expr.num (-1.))) inside);
  check "fallback admits a longer input after all guesses fail" true
    (Expr.Set.add (bin Equal size (Expr.int 3)) inside);
  check "a previous witness cannot fix later positions or ranks" true
    (Expr.Set.add
       (bin Equal pos (Expr.num 1.))
       (Expr.Set.add (bin Equal size (Expr.int 3)) inside));
  let surrogate =
    Expr.Lit
      (Literal.Utf16String
         (Gillian.Utils.Utf16.of_canonical
            (Gillian.Utils.Utf16.of_code_units [ 0xd800 ])))
  in
  check "length witnesses leave code units free" true
    (Expr.Set.add (bin Equal s surrogate) inside);
  (* The actual AJV high-surrogate branch needs a second code unit. Keep
     all the original count/rank/length facts, without fixing either unit. *)
  let next = bin FPlus pos (Expr.num 1.) in
  let first = bin Utf16CodeUnit s (Expr.UnOp (ToIntOp, pos)) in
  let two_inside =
    inside
    |> Expr.Set.add (bin FLessThan next len)
    |> Expr.Set.add (bin Equal next next)
    |> Expr.Set.add (bin Equal first first)
    |> Expr.Set.add (bin FLessThanEqual (Expr.num 55296.) first)
    |> Expr.Set.add (bin FLessThanEqual first (Expr.num 56319.))
  in
  Alcotest.(check bool)
    "model-returning API finds the full second-unit branch" true
    (Option.is_some (Smt.check_sat two_inside gamma));
  (* These SAT controls require feasible strings on both sides of the
     surrogate decision. The full symbolic second-lookup/FP observation
     obligations are separate; these concrete points do not prove them. *)
  List.iter
    (fun second ->
      let text =
        Expr.Lit
          (Literal.Utf16String
             (Gillian.Utils.Utf16.of_canonical
                (Gillian.Utils.Utf16.of_code_units [ 0xd800; second ])))
      in
      check "two-unit feasibility preserves either surrogate outcome" true
        (Expr.Set.add (bin Equal s text) two_inside))
    [ 0xdc00; 0x0041; 0xe000 ];
  check "one unit cannot satisfy the full second-unit branch" false
    (Expr.Set.add (bin Equal size (Expr.int 1)) two_inside);
  check "linked length contradiction survives both length guesses" false
    (Expr.Set.add (bin Equal len (Expr.num 0.)) two_inside);
  check "negative count still rejects the second-unit branch" false
    (Expr.Set.add (bin FLessThan count (Expr.num 0.)) two_inside);
  check "fallback admits a later second-unit branch outside both guesses" true
    (two_inside
    |> Expr.Set.add (bin Equal size (Expr.int 3))
    |> Expr.Set.add (bin Equal pos (Expr.num 1.)));
  (* Exercise either orientation/equality kind without the other link hiding
     which syntactic shape made the optional search eligible. *)
  let unlinked =
    common
    |> Expr.Set.remove (bin ValueEqual len number)
    |> Expr.Set.remove (bin Equal len number)
    |> Expr.Set.add (bin FLessThan pos len)
  in
  let links =
    [
      bin Equal len number;
      bin Equal number len;
      bin ValueEqual len number;
      bin ValueEqual number len;
    ]
  in
  List.iter
    (fun link ->
      check "each direct typed length link admits the branch witness" true
        (Expr.Set.add link unlinked))
    links;
  (* The real helper later keeps the same length equality while dropping
     len's gamma entry. The model-returning path must still see a witness. *)
  Hashtbl.remove gamma "#branch_len";
  Alcotest.(check bool)
    "wrapped linked Number also has a complete-query witness" true
    (Option.is_some (Smt.check_sat inside gamma));
  List.iter
    (fun link ->
      check "either wrapped link retains the full branch formula" true
        (Expr.Set.add link unlinked))
    links;
  check "wrapped length retains the full second-unit branch" true two_inside;
  check "wrapped length does not hide a contradictory full query" false
    (Expr.Set.add (bin Equal size (Expr.int 0)) inside)

let tests =
  [
    Alcotest.test_case "sufficient proof and false goal" `Quick
      (with_total sufficient);
    Alcotest.test_case "SAT subset requires full fallback" `Quick
      (with_total fallback);
    Alcotest.test_case "finite-position native precheck" `Quick
      (with_total finite_position);
    Alcotest.test_case "complete-query SAT witness" `Quick
      (with_total seeded_witness);
    Alcotest.test_case "failed SAT seed requires full fallback" `Quick
      (with_total seeded_fallback);
    Alcotest.test_case "single-pair complete-query witness" `Quick
      (with_total single_pair_witness);
    Alcotest.test_case "length-only complete-query witnesses" `Quick
      (with_total length_only_witness);
  ]
