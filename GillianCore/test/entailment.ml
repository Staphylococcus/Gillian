open Gillian.Gil_syntax
module Gamma = Gillian.Symbolic.Type_env
module Solver = Gillian.Logic.FOSolver
module Config = Gillian.Utils.Config
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let bin op a b = Expr.BinOp (a, op, b)
let not_ e = Expr.UnOp (Not, e)
let x = Expr.LVar "#focus_x"
let y = Expr.LVar "#focus_y"
let z = Expr.LVar "#focus_z"

(* Parse a list of original GIL expression strings into an Expr.Set, failing the
   test on any parse error. This embeds the query417 assertions without a
   runtime /tmp dependency, mirroring the GIL reimport path in utf16_values.ml. *)
let parse_gil_set (strings : string list) : Expr.Set.t =
  List.fold_left
    (fun acc s ->
      match Parser.parse_expression (Lexing.from_string s) with
      | Ok e -> Expr.Set.add e acc
      | Error _ -> failwith ("failed to parse GIL expression: " ^ s))
    Expr.Set.empty strings

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
    Alcotest.(check bool)
      "remembered inconclusive precheck still proves nothing" false
      (Smt.proves_unsat fs g);

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
      (proved || Option.is_none (Smt.check_sat fs g));
    Alcotest.(check bool)
      "actual UNSAT supersedes optional inconclusive marker" true
      (Smt.proves_unsat fs g)

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

let indexed_branch_witness () =
  let s = Expr.LVar "#mask_s" and pos = Expr.LVar "#mask_pos" in
  let len = Expr.LVar "#mask_len" and count = Expr.LVar "#mask_count" in
  let rank = Expr.LVar "#mask_rank" in
  let size = Expr.UnOp (Utf16Len, s) in
  let number = Expr.UnOp (IntToNum, size) in
  let maximum = Expr.num 9007199254740991. in
  let next = bin FPlus pos (Expr.num 1.) in
  let index = Expr.UnOp (ToIntOp, pos) in
  let next_index = Expr.UnOp (ToIntOp, next) in
  let first = bin Utf16CodeUnit s index in
  let second = bin Utf16CodeUnit s next_index in
  let mask =
    bin BitwiseAndF (Expr.UnOp (ToInt32Op, second)) (Expr.num 64512.)
  in
  let low = bin Equal mask (Expr.num 56320.) in
  (* Keep the actual helper query's wrapped count/length/rank and every
     original branch fact. Neither string contents nor position is fixed. *)
  let common =
    Expr.Set.of_list
      [
        not_ (bin FLessThan (Expr.num 56319.) first);
        not_ (bin FLessThan index (Expr.num 0.));
        not_ (bin FLessThan next_index (Expr.num 0.));
        not_ (bin FLessThanEqual number index);
        not_ (bin FLessThanEqual number next_index);
        not_ (bin FLessThan first (Expr.num 55296.));
        Expr.UnOp (IsInt, count);
        Expr.UnOp (IsInt, len);
        Expr.UnOp (IsInt, pos);
        bin FLessThanEqual (Expr.num 0.) count;
        bin FLessThanEqual count pos;
        bin ValueEqual len number;
        bin Equal len len;
        bin Equal len number;
        bin FLessThanEqual len maximum;
        bin ValueEqual rank (bin FMinus maximum pos);
        bin Equal pos pos;
        bin FLessThan pos len;
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
        bin Equal next next;
        bin FLessThan next len;
        bin Equal first first;
      ]
  in
  let g = Gamma.init () in
  Gamma.update g "#mask_s" Type.Utf16Type;
  Gamma.update g "#mask_pos" Type.NumberType;
  let gamma = Gamma.as_hashtbl g in
  let inside = Expr.Set.add low common in
  if Sys.getenv_opt "SMT_TIMEOUT" = Some "1" then
    let rejected =
      try
        ignore (Smt.check_sat inside gamma);
        false
      with
      | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
        msg = "Incomplete totality proof: SMT returned unknown"
    in
    Alcotest.(check bool)
      "position seed cannot hide required unknown" true rejected
  else
    let saved = !Config.dump_smt in
    Config.dump_smt :=
      Option.is_some (Sys.getenv_opt "GILLIAN_UTF16_BRANCH_MODELS");
    Fun.protect
      ~finally:(fun () -> Config.dump_smt := saved)
      (fun () ->
        let check label expected fs =
          Alcotest.(check bool) label expected (Smt.is_sat fs gamma)
        in
        List.iter
          (fun (label, condition) ->
            check label false (Expr.Set.add condition inside))
          [
            ("contradictory mask keeps all original facts", not_ low);
            ( "negative count cannot gain a seeded witness",
              bin FLessThan count (Expr.num 0.) );
            ( "contradictory rank cannot gain a seeded witness",
              bin ValueEqual rank (Expr.num (-1.)) );
            ( "one unit cannot contain the second lookup",
              bin Equal size (Expr.int 1) );
          ];
        let outside_second =
          Expr.Set.add
            (bin FLessThanEqual number next_index)
            (Expr.Set.remove
               (not_ (bin FLessThanEqual number next_index))
               common)
        in
        check "numeric contradiction survives omitted content/count facts" false
          outside_second;
        check "fractional index cannot receive an unproved truncation identity"
          true
          (Expr.Set.of_list
             [
               bin Equal size (Expr.int 1);
               bin ValueEqual pos (Expr.num 0.25);
               bin Equal first (Expr.num 55296.);
               bin FLessThanEqual number next_index;
             ]);
        let cases =
          List.concat_map
            (fun (suffix, extra) ->
              List.map
                (fun (name, result) -> (name ^ suffix, result, extra))
                [ ("low", true); ("other", false) ])
            [
              ("-unrestricted", []);
              ( "-later-three",
                [
                  bin Equal size (Expr.int 3); bin ValueEqual pos (Expr.num 1.);
                ] );
              ( "-later-seven",
                [
                  bin Equal size (Expr.int 7); bin ValueEqual pos (Expr.num 5.);
                ] );
            ]
        in
        let models =
          List.map
            (fun (id, expected, extra) ->
              let fs =
                List.fold_left
                  (fun fs e -> Expr.Set.add e fs)
                  (Expr.Set.add (if expected then low else not_ low) common)
                  extra
              in
              check (id ^ " complete original query remains feasible") true fs;
              (* Fresh typed aliases recover wrapped values without changing
                 the actual context or dropping any original constraint. *)
              let model_gamma = Hashtbl.copy gamma in
              let aliases =
                List.map
                  (fun name -> (name, name ^ "_copy"))
                  [ "#mask_len"; "#mask_count"; "#mask_rank" ]
              in
              let constraints =
                List.fold_left
                  (fun acc (name, copy) ->
                    Hashtbl.add model_gamma copy Type.NumberType;
                    Expr.Set.add
                      (bin ValueEqual (Expr.LVar copy) (Expr.LVar name))
                      acc)
                  fs aliases
              in
              let _initial_model =
                match Smt.check_sat constraints model_gamma with
                | Some model -> model
                | None -> Alcotest.fail ("Missing branch witness: " ^ id)
              in
              (* Force a distinct native context, then retrieve the cached model;
                 lifting must restore the declarations of the original query. *)
              ignore
                (Smt.exec_sat
                   (Expr.Set.singleton (Expr.Lit (Bool true)))
                   (Hashtbl.create 0));
              let model =
                match Smt.check_sat constraints model_gamma with
                | Some cached -> cached
                | None -> Alcotest.fail "Lost cached branch model"
              in
              let lifted = Hashtbl.create 5 in
              Smt.lift_model model model_gamma (Hashtbl.add lifted)
                (Expr.Set.of_list
                   (s :: pos
                   :: List.map (fun (_, copy) -> Expr.LVar copy) aliases));
              let get name =
                match Hashtbl.find_opt lifted name with
                | Some (Expr.Lit value) -> value
                | _ -> Alcotest.fail ("Missing branch model value: " ^ name)
              in
              let values =
                List.map
                  (fun name -> (name, get name))
                  [ "#mask_s"; "#mask_pos" ]
                @ List.concat_map
                    (fun (name, copy) -> [ (name, get copy); (copy, get copy) ])
                    aliases
              in
              let store = Engine.CExprEval.CStore.init values in
              let visitor =
                object
                  inherit [_] Visitors.endo
                  method! visit_LVar () _ name = Expr.PVar name
                end
              in
              Expr.Set.iter
                (fun e ->
                  match
                    Engine.CExprEval.evaluate_expr store
                      (visitor#visit_expr () e)
                  with
                  | Bool true -> ()
                  | _ ->
                      Alcotest.fail
                        "Branch model failed complete concrete replay")
                constraints;
              let bits name =
                match get name with
                | Num n ->
                    `String (Printf.sprintf "%016Lx" (Int64.bits_of_float n))
                | _ -> Alcotest.fail "Branch model lost Number type"
              in
              let units =
                match get "#mask_s" with
                | Utf16String s ->
                    Gillian.Utils.Utf16.(code_units (to_canonical s))
                | _ -> Alcotest.fail "Branch model lost string type"
              in
              `Assoc
                [
                  ("id", `String id);
                  ("low", `Bool expected);
                  ("units", `List (List.map (fun n -> `Int n) units));
                  ("positionBits", bits "#mask_pos");
                  ("lengthBits", bits "#mask_len_copy");
                  ("countBits", bits "#mask_count_copy");
                  ("rankBits", bits "#mask_rank_copy");
                ])
            cases
        in
        match Sys.getenv_opt "GILLIAN_UTF16_BRANCH_MODELS" with
        | None -> ()
        | Some path -> Yojson.Safe.to_file path (`List models))

let contained_goal () =
  let position = Expr.LVar "#contained_pos"
  and bound = Expr.LVar "#contained_bound" in
  let twice = bin FPlus (bin FPlus position (Expr.num 1.)) (Expr.num 1.) in
  let gamma = Gamma.init () in
  Gamma.update gamma "#contained_pos" Type.NumberType;
  Gamma.update gamma "#contained_bound" Type.NumberType;
  let entails facts goal =
    Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
      [ goal ] gamma
  in
  let facts = [ Expr.UnOp (IsInt, position); bin FLessThan position bound ] in
  Alcotest.(check bool)
    "integer double increment uses sufficient contained facts" true
    (entails facts (Expr.UnOp (IsInt, twice)));
  (* The contained subset drops the bound link. The original fallback must
     still use it to prove position < 5. *)
  Alcotest.(check bool)
    "contained SAT still uses dependent full assumptions" true
    (entails
       [ bin FLessThan position bound; bin FLessThanEqual bound (Expr.num 5.) ]
       (bin FLessThan position (Expr.num 5.)));
  Alcotest.(check bool)
    "missing integrality must not prove double increment" false
    (entails
       [ bin ValueEqual position (Expr.num 0.25); bin FLessThan position bound ]
       (Expr.UnOp (IsInt, twice)));
  let text = Expr.LVar "#contained_text" in
  Gamma.update gamma "#contained_text" Type.Utf16Type;
  let code = bin Utf16CodeUnit text (Expr.num 0.) in
  let content =
    [
      bin ILessThan (Expr.int 0) (Expr.UnOp (Utf16Len, text));
      bin Equal code (Expr.num 65.);
      bin Equal position code;
    ]
  in
  Alcotest.(check bool)
    "content-dependent numeric goal retains full fallback" true
    (entails content (bin Equal position (Expr.num 65.)));
  Alcotest.(check bool)
    "wrong content-derived numeric goal remains false" false
    (entails content (bin Equal position (Expr.num 66.)));
  Alcotest.(check bool)
    "direct content goal retains its assumptions" true
    (entails content (bin Equal code (Expr.num 65.)))

let numeric_rank () =
  let position = Expr.LVar "#rank_pos" and len = Expr.LVar "#rank_len" in
  let count = Expr.LVar "#rank_count" and before = Expr.LVar "#rank_before" in
  let text = Expr.LVar "#rank_text" in
  let maximum = Expr.num 9007199254740991. in
  let gamma = Gamma.init () in
  List.iter
    (fun name -> Gamma.update gamma name Type.NumberType)
    [ "#rank_pos"; "#rank_len"; "#rank_count"; "#rank_before" ];
  Gamma.update gamma "#rank_text" Type.Utf16Type;
  let next = bin FPlus position (Expr.num 1.) in
  let twice = bin FPlus next (Expr.num 1.) in
  let base =
    [
      Expr.UnOp (IsInt, position);
      Expr.UnOp (IsInt, len);
      Expr.UnOp (IsInt, count);
      bin FLessThanEqual (Expr.num 0.) count;
      bin FLessThanEqual count position;
      bin FLessThan position len;
      bin FLessThanEqual len maximum;
      bin ValueEqual before (bin FMinus maximum position);
      bin ValueEqual len (Expr.UnOp (IntToNum, Expr.UnOp (Utf16Len, text)));
      bin ILessThanEqual
        (Expr.UnOp (Utf16Len, text))
        (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
      bin FLessThanEqual (Expr.num 55296.)
        (bin Utf16CodeUnit text (Expr.UnOp (ToIntOp, position)));
    ]
  in
  let entails facts goals =
    Solver.check_entailment Utils.Containers.SS.empty (Engine.PFS.of_list facts)
      goals gamma
  in
  List.iter
    (fun (name, after_position, facts) ->
      let rank = bin FMinus maximum after_position in
      Alcotest.(check bool)
        (name ^ " actual Number rank")
        true
        (entails facts
           [
             Expr.UnOp (IsInt, rank);
             bin FLessThanEqual (Expr.num 0.) rank;
             bin FLessThan rank before;
           ]);
      Alcotest.(check bool)
        (name ^ " wrong nondecreasing rank")
        false
        (entails facts [ bin FLessThanEqual before rank ]))
    [
      ("one increment", next, base);
      ("two increments", twice, bin FLessThan next len :: base);
    ]

let numeric_conjuncts () =
  let x = Expr.LVar "#conj_x" and s = Expr.LVar "#conj_s" in
  let limit = Expr.LVar "#conj_limit" in
  let witness = Expr.LVar "#conj_witness" in
  let gamma = Gamma.init () in
  Gamma.update gamma "#conj_x" Type.NumberType;
  Gamma.update gamma "#conj_limit" Type.NumberType;
  Gamma.update gamma "#conj_s" Type.Utf16Type;
  Gamma.update gamma "#conj_witness" Type.NumberType;
  let entails ?(exists = Utils.Containers.SS.empty) facts goals =
    Solver.check_entailment exists (Engine.PFS.of_list facts) goals gamma
  in
  let facts =
    [
      Expr.UnOp (IsInt, x);
      bin FLessThanEqual (Expr.num 0.) x;
      bin FLessThanEqual x limit;
      bin FLessThanEqual limit (Expr.num 10.);
      bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 1);
    ]
  in
  let good = bin FLessThanEqual x (Expr.num 11.) in
  let bad = bin FLessThan x (Expr.num 0.) in
  Alcotest.(check bool)
    "all numeric conjuncts prove" true
    (entails facts [ good; Expr.UnOp (IsInt, bin FPlus x (Expr.num 1.)) ]);
  List.iter
    (fun goals ->
      Alcotest.(check bool)
        "one true conjunct cannot hide a false conjunct" false
        (entails facts goals))
    [ [ good; bad ]; [ bad; good ] ];
  let contents =
    [
      bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 1);
      bin ValueEqual x (bin Utf16CodeUnit s (Expr.num 0.));
      bin Equal (bin Utf16CodeUnit s (Expr.num 0.)) (Expr.num 65.);
    ]
  in
  Alcotest.(check bool)
    "inconclusive numeric pieces retain content-dependent fallback" true
    (entails contents
       [ bin FLessThanEqual (Expr.num 0.) x; bin Equal x (Expr.num 65.) ]);
  Alcotest.(check bool)
    "existential conjuncts must share one witness" false
    (entails
       ~exists:(Utils.Containers.SS.singleton "#conj_witness")
       facts
       [
         bin FLessThanEqual (Expr.num 0.) witness;
         bin FLessThanEqual witness (Expr.num (-1.));
       ])

let last_unit_witness () =
  let names =
    [
      "#tail_oldpos";
      "#tail_oldcount";
      "#tail_pos";
      "#tail_count";
      "#tail_len";
      "#tail_rank";
      "#tail_value";
    ]
  in
  let oldpos = Expr.LVar "#tail_oldpos"
  and oldcount = Expr.LVar "#tail_oldcount" in
  let pos = Expr.LVar "#tail_pos" and count = Expr.LVar "#tail_count" in
  let len = Expr.LVar "#tail_len" and rank = Expr.LVar "#tail_rank" in
  let value = Expr.LVar "#tail_value" and s = Expr.LVar "#tail_s" in
  let size = Expr.UnOp (Utf16Len, s) in
  let index = Expr.UnOp (ToIntOp, oldpos) in
  let code = bin Utf16CodeUnit s index in
  let maximum = Expr.num 9007199254740991. in
  let facts =
    Expr.Set.of_list
      [
        Expr.UnOp (IsInt, oldpos);
        Expr.UnOp (IsInt, oldcount);
        Expr.UnOp (IsInt, pos);
        Expr.UnOp (IsInt, count);
        Expr.UnOp (IsInt, len);
        bin FLessThanEqual (Expr.num 0.) oldcount;
        bin FLessThanEqual oldcount oldpos;
        bin FLessThan oldpos len;
        bin FLessThanEqual len maximum;
        bin ValueEqual len (Expr.UnOp (IntToNum, size));
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
        bin ValueEqual rank (bin FMinus maximum oldpos);
        bin ValueEqual pos (bin FPlus oldpos (Expr.num 1.));
        bin ValueEqual count (bin FPlus oldcount (Expr.num 1.));
        bin FLessThanEqual (Expr.num 0.) count;
        bin FLessThanEqual count pos;
        bin FLessThanEqual pos len;
        not_ (bin FLessThan pos len);
        bin FLessThanEqual (Expr.num 55296.) code;
        bin FLessThanEqual code (Expr.num 56319.);
        bin ValueEqual value code;
      ]
  in
  let gamma = Hashtbl.create 8 in
  List.iter (fun name -> Hashtbl.add gamma name Type.NumberType) names;
  Hashtbl.add gamma "#tail_s" Type.Utf16Type;
  let model =
    match Smt.check_sat facts gamma with
    | Some model -> model
    | None -> Alcotest.fail "Missing full-context last-unit witness"
  in
  let vars =
    Expr.Set.of_list
      (List.map (fun name -> Expr.LVar name) ("#tail_s" :: names))
  in
  let lifted = Hashtbl.create 8 in
  Smt.lift_model model gamma (Hashtbl.add lifted) vars;
  let values =
    List.map
      (fun name ->
        match Hashtbl.find_opt lifted name with
        | Some (Expr.Lit value) -> (name, value)
        | _ -> Alcotest.fail ("Missing last-unit model value: " ^ name))
      ("#tail_s" :: names)
  in
  let store = Engine.CExprEval.CStore.init values in
  let visitor =
    object
      inherit [_] Visitors.endo
      method! visit_LVar () _ name = Expr.PVar name
    end
  in
  Expr.Set.iter
    (fun e ->
      match Engine.CExprEval.evaluate_expr store (visitor#visit_expr () e) with
      | Bool true -> ()
      | _ -> Alcotest.fail "Last-unit witness failed original-context replay")
    facts;
  List.iter
    (fun (label, bad) ->
      Alcotest.(check bool)
        label false
        (Smt.is_sat (Expr.Set.add bad facts) gamma))
    [
      ("negative count remains contradictory", bin FLessThan count (Expr.num 0.));
      ( "negative saved rank remains contradictory",
        bin ValueEqual rank (Expr.num (-1.)) );
      ( "empty string cannot contain the last lookup",
        bin Equal size (Expr.int 0) );
    ]

let model_declarations () =
  let make tag n =
    let name = "ModelContext" ^ tag and cname = "ModelBox" ^ tag in
    let constructor : Constructor.t =
      {
        constructor_name = cname;
        constructor_source_path = None;
        constructor_loc = None;
        constructor_num_fields = 1;
        constructor_fields = [ Some Type.NumberType ];
        constructor_datatype = name;
      }
    in
    let datatype : Datatype.t =
      {
        datatype_name = name;
        datatype_source_path = None;
        datatype_loc = None;
        datatype_constructors = [ constructor ];
      }
    in
    let table = Hashtbl.create 1 in
    Hashtbl.add table name datatype;
    let env = Prog_env.Datatype_env.make' table in
    let number = Expr.LVar ("#model_number_" ^ tag) in
    let wrapped = Expr.LVar ("#model_wrapped_" ^ tag) in
    let value = Expr.LVar ("#model_custom_" ^ tag) in
    let gamma = Hashtbl.create 1 in
    (match number with
    | LVar name -> Hashtbl.add gamma name Type.NumberType
    | _ -> assert false);
    let fs =
      Expr.Set.of_list
        [
          bin ValueEqual number (Expr.num n);
          bin ValueEqual wrapped number;
          bin Equal value (Expr.ConstructorApp (cname, [ number ]));
        ]
    in
    let run check =
      Prog_env.Datatype_env.using env (fun () ->
          match check fs gamma with
          | Some model -> model
          | None -> Alcotest.fail "Missing datatype model")
    in
    (number, gamma, run, n)
  in
  let a, ga, run_a, na = make "A" (-0.) in
  let b, gb, run_b, nb = make "B" 42. in
  let ma = run_a Smt.check_sat in
  let mb = run_b Smt.check_sat in
  let replay x gamma expected model =
    let lifted = Hashtbl.create 1 in
    Smt.lift_model model gamma (Hashtbl.add lifted) (Expr.Set.singleton x);
    let name =
      match x with
      | LVar name -> name
      | _ -> assert false
    in
    let actual =
      match Hashtbl.find_opt lifted name with
      | Some (Expr.Lit (Num n)) -> Int64.bits_of_float n
      | _ -> Alcotest.fail "Missing Number after datatype restoration"
    in
    Alcotest.(check int64)
      "original model survives distinct context and reset"
      (Int64.bits_of_float expected)
      actual
  in
  replay a ga na ma;
  replay b gb nb mb;
  replay a ga na (run_a Smt.check_sat);
  (* Bypass the SAT cache to exercise cached query encoding with its original
     custom datatype declarations, then lift outside any datatype handler. *)
  replay b gb nb (run_b (fun fs gamma -> Smt.exec_sat fs gamma));
  replay a ga na ma

let relevant_types () =
  let a = Expr.LVar "#relevant_a" in
  let b = Expr.LVar "#relevant_b" in
  let c = Expr.LVar "#relevant_c" in
  let focus =
    (Utils.Containers.SS.empty, Expr.lvars a, Utils.Containers.SS.empty)
  in
  let facts = [ bin ValueEqual a b; bin ValueEqual b c ] in
  let g = Gamma.init () in
  Gamma.update g "#relevant_a" Type.NumberType;
  Gamma.update g "#relevant_c" Type.BooleanType;
  let before = Gamma.to_list g |> List.sort compare in
  Alcotest.(check bool)
    "transitively retained formulas preserve their known types" false
    (Solver.check_satisfiability ~relevant_info:focus facts g);
  Alcotest.(check bool)
    "relevance checking leaves caller types unchanged" true
    (before = (Gamma.to_list g |> List.sort compare));
  Gamma.remove g "#relevant_c";
  Gamma.update g "#relevant_c" Type.NumberType;
  Alcotest.(check bool)
    "consistent transitive aliases remain feasible" true
    (Solver.check_satisfiability ~relevant_info:focus facts g);
  let zero = bin ValueEqual a (Expr.num 0.) in
  let one = bin ValueEqual c (Expr.num 1.) in
  Alcotest.(check bool)
    "retained transitive contradiction still rejects" false
    (Solver.check_satisfiability ~relevant_info:focus (zero :: one :: facts) g)

let invariant_counter_witness () =
  let s = Expr.LVar "#invariant_s" and pos = Expr.LVar "#invariant_pos" in
  let count = Expr.LVar "#invariant_count"
  and len = Expr.LVar "#invariant_len" in
  let after = Expr.LVar "#invariant_after" in
  let next_count = Expr.LVar "#invariant_next_count" in
  let rank = Expr.LVar "#invariant_rank" in
  let size = Expr.UnOp (Utf16Len, s) in
  let next = bin FPlus pos (Expr.num 1.) in
  let first = bin Utf16CodeUnit s (Expr.UnOp (ToIntOp, pos)) in
  let second = bin Utf16CodeUnit s (Expr.UnOp (ToIntOp, next)) in
  let fs =
    Expr.Set.of_list
      [
        bin ValueEqual len (Expr.UnOp (IntToNum, size));
        bin ILessThanEqual size
          (Expr.Lit (Int (Z.pred (Z.shift_left Z.one 53))));
        Expr.UnOp (IsInt, count);
        Expr.UnOp (IsInt, pos);
        Expr.UnOp (IsInt, len);
        not_ (bin ValueEqual pos (Expr.num (-0.)));
        not_ (bin ValueEqual len (Expr.num (-0.)));
        bin FLessThanEqual (Expr.num 0.) count;
        bin FLessThanEqual count pos;
        bin FLessThan pos len;
        bin FLessThan next len;
        bin FLessThanEqual (Expr.num 55296.) first;
        bin FLessThanEqual first (Expr.num 56319.);
        bin Equal
          (bin BitwiseAndF (Expr.UnOp (ToInt32Op, second)) (Expr.num 64512.))
          (Expr.num 56320.);
        bin ValueEqual after (bin FPlus next (Expr.num 1.));
        bin ValueEqual next_count (bin FPlus count (Expr.num 1.));
        bin ValueEqual rank (bin FMinus (Expr.num 9007199254740991.) pos);
        Expr.UnOp (IsInt, after);
        Expr.UnOp (IsInt, next_count);
        bin FLessThanEqual next_count after;
        bin FLessThanEqual after len;
      ]
  in
  let g = Gamma.init () in
  Gamma.update g "#invariant_s" Type.Utf16Type;
  List.iter
    (fun name -> Gamma.update g name Type.NumberType)
    [
      "#invariant_pos";
      "#invariant_count";
      "#invariant_len";
      "#invariant_after";
      "#invariant_next_count";
      "#invariant_rank";
    ];
  let gamma = Gamma.as_hashtbl g in
  let check label expected facts =
    Alcotest.(check bool) label expected (Smt.is_sat facts gamma)
  in
  check "complete invariant with derived count and rank is feasible" true fs;
  check "negative counter cannot gain a root witness" false
    (Expr.Set.add (bin FLessThan count (Expr.num 0.)) fs);
  check "incorrect derived count remains contradictory" false
    (Expr.Set.add
       (not_ (bin ValueEqual next_count (bin FPlus count (Expr.num 1.))))
       fs);
  check "nonzero counter and later position survive failed zero guesses" true
    (fs
    |> Expr.Set.add (bin ValueEqual count (Expr.num 1.))
    |> Expr.Set.add (bin ValueEqual pos (Expr.num 1.))
    |> Expr.Set.add (bin Equal size (Expr.int 3)))

(* Source query417, SHA
   84f4b79835e95e5f538d54401a8929a224f87ae60a48ee8b7f846c221ca9d8eb. The
   native full query SIGSEGVs; the exact unchanged arithmetic subset is UNSAT.
   The precheck must decide UNSAT on the unchanged numeric subset before any
   mixed-query witness search (no native exec_sat on this full set). *)
let mixed_numeric_reproducer () =
  let strings =
    [
      "(! (#pos == 0.))";
      "(is_int #lvar_249)";
      "(is_int #pos)";
      "(is_int #zeroPrevious)";
      "(is_int #zeroPreviousCount)";
      "(0. == (#zeroPreviousCount + 1.))";
      "(0. <= #lvar_249)";
      "(0. <= #pos)";
      "(0. <= #zeroPrevious)";
      "(0. <= #zeroPreviousCount)";
      "(55296. <= u16-code(#s, (num_to_int #lvar_249)))";
      "(55296. <= u16-code(#s, (num_to_int #zeroPrevious)))";
      "(#len == (as_num (u16-len #s)))";
      "(#lvar_249 < #zeroPrevious)";
      "(#pos == (#zeroPrevious + 1.))";
      "(#pos <= #len)";
      "(#zeroPrevious == (#lvar_249 + 1.))";
      "(#zeroPrevious < #pos)";
      "(#zeroPrevious <= #len)";
      "(#zeroPreviousCount == (#lvar_250 + 1.))";
      "(#zeroPreviousCount <= #zeroPrevious)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#lvar_249 + 1.) < #len)";
      "(u16-code(#s, (num_to_int #lvar_249)) <= 56319.)";
      "(u16-code(#s, (num_to_int #zeroPrevious)) <= 56319.)";
      "((#zeroPrevious + 1.) < #len)";
      "((u16-code(#s, (num_to_int (#lvar_249 + 1.))) < 56320.) or (57343. < \
       u16-code(#s, (num_to_int (#lvar_249 + 1.)))))";
      "((u16-code(#s, (num_to_int (#zeroPrevious + 1.))) < 56320.) or (57343. \
       < u16-code(#s, (num_to_int (#zeroPrevious + 1.)))))";
    ]
  in
  let fs = parse_gil_set strings in
  let g = Gamma.init () in
  Gamma.update g "#s" Type.Utf16Type;
  List.iter
    (fun name -> Gamma.update g name Type.NumberType)
    [
      "#lvar_250";
      "#pos";
      "#len";
      "#zeroPreviousCount";
      "#zeroPrevious";
      "#lvar_249";
    ];
  let gamma = Gamma.as_hashtbl g in
  Alcotest.(check bool)
    "mixed numeric contradiction decided on the unchanged numeric subset" true
    (Option.is_none (Smt.check_sat fs gamma))

let numeric_sat_full_witness () =
  let x = Expr.LVar "#num_sat_x" and s = Expr.LVar "#num_sat_s" in
  let g = Gamma.init () in
  Gamma.update g "#num_sat_x" Type.NumberType;
  Gamma.update g "#num_sat_s" Type.Utf16Type;
  let gamma = Gamma.as_hashtbl g in
  let fs =
    Expr.Set.of_list
      [
        bin ValueEqual x (Expr.num 1.);
        bin Equal s
          (Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "A")));
      ]
  in
  Alcotest.(check bool)
    "numeric subset SAT cannot be treated as a complete-query UNSAT" true
    (Option.is_some (Smt.check_sat fs gamma))

let numeric_sat_string_contradiction () =
  let x = Expr.LVar "#num_len_x" and s = Expr.LVar "#num_len_s" in
  let g = Gamma.init () in
  Gamma.update g "#num_len_x" Type.NumberType;
  Gamma.update g "#num_len_s" Type.Utf16Type;
  let gamma = Gamma.as_hashtbl g in
  let fs =
    Expr.Set.of_list
      [
        bin ValueEqual x (Expr.num 0.);
        bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 1);
        bin Equal (Expr.UnOp (Utf16Len, s)) (Expr.int 2);
      ]
  in
  Alcotest.(check bool)
    "a numeric-only model is not a complete-query witness" true
    (Option.is_none (Smt.check_sat fs gamma))

let numeric_precheck_binary64_rounding () =
  let x = Expr.LVar "#num_rnd_x" and s = Expr.LVar "#num_rnd_s" in
  let g = Gamma.init () in
  Gamma.update g "#num_rnd_x" Type.NumberType;
  Gamma.update g "#num_rnd_s" Type.Utf16Type;
  let gamma = Gamma.as_hashtbl g in
  let fs =
    Expr.Set.of_list
      [
        bin ValueEqual x (Expr.num 9007199254740992.);
        bin ValueEqual (bin FPlus x (Expr.num 1.)) x;
        bin Equal s
          (Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "A")));
      ]
  in
  Alcotest.(check bool)
    "binary64 rounding is not rejected by a strict-increment shortcut" true
    (Option.is_some (Smt.check_sat fs gamma))

let empty_length_preserves_derived_rank () =
  (* The 28 original GIL strings reconstruct query902: an empty-string state
     with saved rank MAX_SAFE_INTEGER. The diagnostic GIL printer rounds that
     bound, so the two literals were restored to the exact 9007199254740991.
     from the SMT binary64 bits 433fffffffffffff (preparation.json). No
     runtime /tmp dependency. *)
  let strings =
    [
      "(! (#len v== -0.))";
      "(! (#len < #len))";
      "(! (#value == none))";
      "(is_int #count)";
      "(is_int #len)";
      "(0. <= #count)";
      "(#count == 0.)";
      "(#count < 1.)";
      "(#count <= #len)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == 0.)";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_262 v== (9007199254740991. - #len))";
      "(#lvar_js_0 v== #lvar_js_12)";
      "(#lvar_js_0 v== #lvar_js_4)";
      "(#lvar_js_1 v== #lvar_js_13)";
      "(#lvar_js_1 v== #lvar_js_5)";
      "(#lvar_js_12 v== #lvar_js_0)";
      "(#lvar_js_13 v== #lvar_js_1)";
      "(#lvar_js_14 v== #lvar_js_2)";
      "(#lvar_js_2 v== #lvar_js_14)";
      "(#lvar_js_2 v== #lvar_js_6)";
      "(#lvar_js_4 v== #lvar_js_0)";
      "(#lvar_js_5 v== #lvar_js_1)";
      "(#lvar_js_6 v== #lvar_js_2)";
      "((u16-len #s) i<= 9007199254740991i)";
    ]
  in
  let fs = parse_gil_set strings in
  let g = Gamma.init () in
  Gamma.update g "#s" Type.Utf16Type;
  List.iter
    (fun n -> Gamma.update g n Type.NumberType)
    [ "#len"; "#count"; "#lvar_262" ];
  let gamma = Gamma.as_hashtbl g in
  let s = Expr.LVar "#s" in
  let max_rank_bits = Int64.bits_of_float 9007199254740991. in
  let one_rank_bits = Int64.bits_of_float 9007199254740990. in
  let lifted model =
    let t = Hashtbl.create 4 in
    Smt.lift_model model gamma (Hashtbl.add t)
      (Expr.Set.of_list
         (List.map
            (fun name -> Expr.LVar name)
            [ "#s"; "#len"; "#count"; "#lvar_262" ]));
    let get name =
      match Hashtbl.find_opt t name with
      | Some (Expr.Lit value) -> value
      | _ -> Alcotest.fail ("Missing lifted model value: " ^ name)
    in
    get
  in
  (* Control A: the original fs must admit a native full-query model. The
     empty-length witness search must find it without fixing the derived
     Number variables: s is empty, len/count are 0, and rank keeps its exact
     MAX_SAFE_INTEGER bits. A bare all-zero guess is invalid, so this rank
     assertion is the load-bearing check. *)
  match Smt.check_sat fs gamma with
  | Some model -> (
      let get = lifted model in
      Alcotest.(check bool)
        "empty witness: s is the empty Utf16 string" true
        (get "#s" = Literal.Utf16String (Gillian.Utils.Utf16.of_canonical ""));
      Alcotest.(check int64)
        "empty witness: len is numerical 0" 0L
        (Int64.bits_of_float
           (match get "#len" with
           | Literal.Num n -> n
           | _ -> Alcotest.fail "len lost Number type"));
      Alcotest.(check int64)
        "empty witness: count is numerical 0" 0L
        (Int64.bits_of_float
           (match get "#count" with
           | Literal.Num n -> n
           | _ -> Alcotest.fail "count lost Number type"));
      Alcotest.(check int64)
        "empty witness: rank retains MAX_SAFE_INTEGER bits" max_rank_bits
        (Int64.bits_of_float
           (match get "#lvar_262" with
           | Literal.Num n -> n
           | _ -> Alcotest.fail "rank lost Number type"));
      (* Control B: an original s == u16"A" contradicts the zero length, so
         the complete query must reject and the empty seed cannot ignore the
         original string facts. *)
      Alcotest.(check bool)
        "original string facts reject a non-empty witness" true
        (Option.is_none
           (Smt.check_sat
              (Expr.Set.add
                 (bin Equal s
                    (Expr.Lit
                       (Literal.Utf16String
                          (Gillian.Utils.Utf16.of_canonical "A"))))
                 fs)
              gamma));
      (* Control C: remove exactly the "#len == 0." fact, add "#len == 1."
         plus s == u16"A". The original rank relation (#lvar_262 v==
         9007199254740991. - #len) stays in the query, so the witness rank is
         now MAX - 1. This proves a failed empty guess falls back rather than
         narrowing later states to empty strings. *)
      let len = Expr.LVar "#len" in
      let len_zero = bin Equal len (Expr.num 0.) in
      assert (Expr.Set.mem len_zero fs);
      let fs1 =
        Expr.Set.add
          (bin Equal len (Expr.num 1.))
          (Expr.Set.add
             (bin Equal s
                (Expr.Lit
                   (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "A"))))
             (Expr.Set.remove len_zero fs))
      in
      match Smt.check_sat fs1 gamma with
      | Some model ->
          let get = lifted model in
          Alcotest.(check int64)
            "fallback witness: rank retains the original relation" one_rank_bits
            (Int64.bits_of_float
               (match get "#lvar_262" with
               | Literal.Num n -> n
               | _ -> Alcotest.fail "rank lost Number type"))
      | None ->
          Alcotest.fail
            "a non-empty length with a non-empty string must be satisfiable")
  | None -> Alcotest.fail "Missing complete-query empty-length witness"

let length_zero_core () =
  (* The 36 original GIL expressions from AJV query829: an empty-string state
     with saved rank and structural JS aliases. Two rounded Num literals are
     restored to the exact 9007199254740991. from the SMT binary64 bits
     433fffffffffffff, as the query902 test does. No runtime /tmp dependency. *)
  let strings =
    [
      "(! (#len v== -0.))";
      "(! (#len < #len))";
      "(! (#lvar_262 == empty))";
      "(! (#value == none))";
      "(! ((u16-len #s) == 0i))";
      "(is_int #count)";
      "(is_int #len)";
      "(0. <= #count)";
      "(#count == 0.)";
      "(#count < 1.)";
      "(#count <= #len)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == 0.)";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_263 v== (9007199254740991. - #len))";
      "(#lvar_js_0 v== #lvar_js_12)";
      "(#lvar_js_0 v== #lvar_js_16)";
      "(#lvar_js_0 v== #lvar_js_4)";
      "(#lvar_js_1 v== #lvar_js_13)";
      "(#lvar_js_1 v== #lvar_js_17)";
      "(#lvar_js_1 v== #lvar_js_5)";
      "(#lvar_js_12 v== #lvar_js_0)";
      "(#lvar_js_13 v== #lvar_js_1)";
      "(#lvar_js_14 v== #lvar_js_2)";
      "(#lvar_js_16 v== #lvar_js_0)";
      "(#lvar_js_17 v== #lvar_js_1)";
      "(#lvar_js_18 v== #lvar_js_2)";
      "(#lvar_js_2 v== #lvar_js_14)";
      "(#lvar_js_2 v== #lvar_js_18)";
      "(#lvar_js_2 v== #lvar_js_6)";
      "(#lvar_js_4 v== #lvar_js_0)";
      "(#lvar_js_5 v== #lvar_js_1)";
      "(#lvar_js_6 v== #lvar_js_2)";
      "((u16-len #s) i<= 9007199254740991i)";
    ]
  in
  let fs = parse_gil_set strings in
  let goal = bin Equal (Expr.UnOp (Utf16Len, Expr.LVar "#s")) (Expr.int 0) in
  let neg_goal = Expr.negate goal in
  (* The negated empty-length goal is one of the 36 original expressions. *)
  assert (Expr.Set.mem neg_goal fs);
  let facts = Expr.Set.remove neg_goal fs in
  let fresh_gamma () =
    let g = Gamma.init () in
    Gamma.update g "#s" Type.Utf16Type;
    List.iter
      (fun n -> Gamma.update g n Type.NumberType)
      [ "#len"; "#count"; "#lvar_263" ];
    g
  in
  let entail fs' goal' =
    Solver.check_entailment Utils.Containers.SS.empty
      (Engine.PFS.of_list (Expr.Set.elements fs'))
      [ goal' ] (fresh_gamma ())
  in
  let len_link op =
    bin op (Expr.LVar "#len")
      (Expr.UnOp (IntToNum, Expr.UnOp (Utf16Len, Expr.LVar "#s")))
  in
  let s_is_a =
    bin Equal (Expr.LVar "#s")
      (Expr.Lit (Literal.Utf16String (Gillian.Utils.Utf16.of_canonical "A")))
  in
  (* A. All original facts imply the empty-length goal: the new sufficient
     path proves it from the four-expression subset. Reproduce the former
     complete-query unknown with original rank and structural aliases kept. *)
  Alcotest.(check bool)
    "original facts imply the empty-length goal" true (entail facts goal);
  (* B. The same facts do NOT imply the opposite (nonempty length). *)
  Alcotest.(check bool)
    "original facts do not imply a nonempty length" false
    (entail facts (Expr.negate goal));
  (* C. Dropping both original length links and pinning a nonempty string is a
     concrete full-query counterexample: the empty-length goal no longer holds. *)
  let eq_link = len_link Equal in
  let v_link = len_link ValueEqual in
  assert (Expr.Set.mem eq_link facts);
  assert (Expr.Set.mem v_link facts);
  let facts_c =
    Expr.Set.add s_is_a (Expr.Set.remove eq_link (Expr.Set.remove v_link facts))
  in
  Alcotest.(check bool)
    "missing length links reject the empty-length goal" false
    (entail facts_c goal);
  (* D. Keeping the links but removing only the zero equation and pinning a
     nonempty length + nonempty string is a separate concrete witness: the
     rejection stays decisive without touching the production inputs. *)
  let len_zero = bin Equal (Expr.LVar "#len") (Expr.num 0.) in
  assert (Expr.Set.mem len_zero facts);
  let facts_d =
    Expr.Set.add
      (bin Equal (Expr.LVar "#len") (Expr.num 1.))
      (Expr.Set.add s_is_a (Expr.Set.remove len_zero facts))
  in
  Alcotest.(check bool)
    "missing zero equation rejects the empty-length goal" false
    (entail facts_d goal)

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
    Alcotest.test_case "model datatype context survives reset and caches" `Quick
      (with_total model_declarations);
    Alcotest.test_case "indexed complete-query witnesses" `Quick
      (with_total indexed_branch_witness);
    Alcotest.test_case "contained goal preserves required fallback" `Quick
      (with_total contained_goal);
    Alcotest.test_case "numeric rank retains original dependencies" `Quick
      (with_total numeric_rank);
    Alcotest.test_case "last-unit witness retains complete invariant" `Quick
      (with_total last_unit_witness);
    Alcotest.test_case "numeric conjuncts preserve rejection and fallback"
      `Quick
      (with_total numeric_conjuncts);
    Alcotest.test_case "relevance preserves transitive types" `Quick
      (with_total relevant_types);
    Alcotest.test_case "invariant counters preserve complete witness queries"
      `Quick
      (with_total invariant_counter_witness);
    Alcotest.test_case "mixed numeric contradiction reproducer" `Quick
      (with_total mixed_numeric_reproducer);
    Alcotest.test_case "numeric SAT requires full SAT witness" `Quick
      (with_total numeric_sat_full_witness);
    Alcotest.test_case "numeric SAT retains string contradiction" `Quick
      (with_total numeric_sat_string_contradiction);
    Alcotest.test_case "numeric precheck preserves binary64 rounding" `Quick
      (with_total numeric_precheck_binary64_rounding);
    Alcotest.test_case "empty length preserves derived rank and fallback" `Quick
      (with_total empty_length_preserves_derived_rank);
    Alcotest.test_case "empty-length core sufficient check and rejections"
      `Quick
      (with_total length_zero_core);
  ]
