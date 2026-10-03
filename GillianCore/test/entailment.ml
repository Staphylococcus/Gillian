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
    (* This resource-control invocation runs alone in a fresh test directory.
       Check both the rejection semantics and visibility without verbose logs. *)
    let module L = Logging in
    L.Mode.set_mode (Enabled Normal);
    L.initialize [ L.file_reporter ];
    Fun.protect
      ~finally:(fun () ->
        L.wrap_up ();
        L.initialize [];
        L.Mode.set_mode (Enabled Verbose))
      (fun () ->
        L.verbose (fun m -> m "UNKNOWN_CONTROL_VERBOSE_SENTINEL");
        let trace = L.Loggable.make_string "UNKNOWN_CONTROL_COMMAND_TRACE" in
        let trace_type = L.Logging_constants.Content_type.cmd in
        ignore (L.Specific.normal trace trace_type);
        let reduction = bin IPlus (Expr.int 9001) (Expr.int 1) in
        let expected = Expr.int 9002 in
        let reduction_line =
          Fmt.str "reduce_lexpr: @[%a -> %a@]" Expr.pp reduction Expr.pp expected
        in
        Alcotest.(check bool) "normal reduction preserves result" true
          (Expr.equal (Engine.Reduction.reduce_lexpr reduction) expected);
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
          (rejected (fun () -> ignore (Smt.is_sat single_pair g)));
        let ch = open_in_bin "file.log" in
        let log = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        let lines = String.split_on_char '\n' log in
        Alcotest.(check bool) "unknown remains visible at normal logging" true
          (List.mem "The solver returned: unknown" lines);
        Alcotest.(check bool) "verbose tracing really is disabled" false
          (List.mem "UNKNOWN_CONTROL_VERBOSE_SENTINEL" lines);
        Alcotest.(check bool) "normal file logging omits command traces" false
          (List.mem "UNKNOWN_CONTROL_COMMAND_TRACE" lines);
        Alcotest.(check bool) "normal file logging omits reduction traces" false
          (List.mem reduction_line lines);
        L.Mode.set_mode (Enabled Verbose);
        ignore (L.Specific.normal trace trace_type);
        Alcotest.(check bool) "verbose reduction preserves result" true
          (Expr.equal (Engine.Reduction.reduce_lexpr reduction) expected);
        let ch = open_in_bin "file.log" in
        let verbose_log = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        let verbose_lines = String.split_on_char '\n' verbose_log in
        Alcotest.(check bool) "verbose file logging retains command traces" true
          (List.mem "UNKNOWN_CONTROL_COMMAND_TRACE" verbose_lines);
        Alcotest.(check bool) "verbose file logging retains reduction traces" true
          (List.mem reduction_line verbose_lines)))
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
  let run () =
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
  in
  let saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) run

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

let utf16_code_order_core () =
  (* Original q280 entailment premises. Restore MAX_SAFE_INTEGER from its
     exact binary64 bits, not the rounded decimal log printer. No new facts. *)
  let facts = parse_gil_set
    [
      "(#len == (as_num (u16-len #s)))";
      "(#pos == #pos)";
      "(#len == #len)";
      "(#this == undefined)";
      "((u16-len #s) i<= 9007199254740991i)";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #pos)";
      "(0. <= #count)";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_437 v== (9007199254740991. - #pos))";
      "(#pos < #len)";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== ((#pos + 1.) + 1.))";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(is_int #next_pos)";
      "(is_int (#count + 1.))";
      "(0. <= (#count + 1.))";
      "((#count + 1.) <= #next_pos)";
    ]
  in
  let s = Expr.LVar "#s" and pos = Expr.LVar "#pos" in
  let code = bin Utf16CodeUnit s (Expr.UnOp (ToIntOp, pos)) in
  let lower = Expr.num 55296. in
  let goal = bin FLessThanEqual lower code in
  let premise = not_ (bin FLessThan code lower) in
  assert (Expr.Set.mem premise facts);
  let fresh_gamma () =
    let g = Gamma.init () in
    Gamma.update g "#s" Type.Utf16Type;
    Gamma.update g "#this" Type.UndefinedType;
    List.iter (fun n -> Gamma.update g n Type.NumberType)
      [ "#pos"; "#len"; "#count"; "#next_pos"; "#lvar_437" ];
    g
  in
  let entail fs goal =
    Solver.check_entailment Utils.Containers.SS.empty
      (Engine.PFS.of_list (Expr.Set.elements fs)) [ goal ] (fresh_gamma ())
  in
  let queries () =
    if Sys.file_exists "gillian_smt_queries" then
      Array.to_list (Sys.readdir "gillian_smt_queries")
    else []
  in
  let before = queries () in
  let saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) "original lower-bound entailment" true
      (entail facts goal);
    (* Require the actual original two-atom native query. An always-success
       stub emits no query; the prior complete-query path emits larger sets. *)
    let core = Expr.Set.of_list [ Expr.negate goal; premise ] in
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
        (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) core in
    let fresh = List.filter (fun name -> not (List.mem name before)) (queries ()) in
    Alcotest.(check int) "one native query establishes the entailment" 1
      (List.length fresh);
    let observed = List.filter (fun name ->
      let path = Filename.concat "gillian_smt_queries" name in
      let ch = open_in_bin path in
      let contents = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix contents) fresh in
    Alcotest.(check int) "one original-fact native core query" 1
      (List.length observed);
    Printf.printf "UTF16_ORDER_CORE_NATIVE_QUERY=%s\n%!" (List.hd observed);
    let literal units = Expr.Lit (Literal.Utf16String
        (Gillian.Utils.Utf16.of_canonical
           (Gillian.Utils.Utf16.of_code_units units))) in
    let concrete units = Expr.Set.of_list
        [ bin Equal s (literal units); bin Equal pos (Expr.num 0.) ] in
    let low = Expr.Set.add premise (concrete [55296; 65]) in
    Alcotest.(check bool) "nearby stronger bound has a counterexample" false
      (entail low (bin FLessThanEqual (Expr.num 55297.) code));
    Alcotest.(check bool) "missing premise retains a counterexample" false
      (entail (concrete [65]) goal);
    let next = bin Utf16CodeUnit s (Expr.num 1.) in
    Alcotest.(check bool) "another access cannot borrow the premise" false
      (entail low (bin FLessThanEqual lower next));
    let g = fresh_gamma () |> Gamma.as_hashtbl in
    let sat_core = Expr.Set.of_list
        [ premise; not_ (bin FLessThanEqual (Expr.num 55297.) code) ] in
    Alcotest.(check bool) "SAT core is inconclusive, not proof" false
      (Smt.proves_unsat sat_core g);
    Alcotest.(check bool) "same core has a native SAT model" true
      (Option.is_some (Smt.exec_sat sat_core g)))


(* These tests call the shared SAT path on retained helper queries, including
   branch infeasibility. Native core observation rejects an always-success or
   registry-only implementation; explicit SAT models reject always-UNSAT. *)
let observe_original_core label facts expected gamma =
  let queries () =
    if Sys.file_exists "gillian_smt_queries" then
      Array.to_list (Sys.readdir "gillian_smt_queries") else []
  in
  let before = queries () and saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) (label ^ " original query is UNSAT") true
      (Option.is_none (Smt.check_sat facts (Gamma.as_hashtbl gamma)));
    let fresh = List.filter (fun name -> not (List.mem name before)) (queries ()) in
    Alcotest.(check int) (label ^ " one native core query") 1 (List.length fresh);
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) expected in
    let path = Filename.concat "gillian_smt_queries" (List.hd fresh) in
    let ch = open_in_bin path in
    let contents = Fun.protect ~finally:(fun () -> close_in ch)
      (fun () -> really_input_string ch (in_channel_length ch)) in
    Alcotest.(check bool) (label ^ " exact original atoms observed") true
      (String.starts_with ~prefix contents);
    Printf.printf "ORIGINAL_CORE_NATIVE_QUERY=%s:%s\n%!" label (List.hd fresh))

let original_core_gamma () =
  let g = Gamma.init () in
  Gamma.update g "#s" Type.Utf16Type;
  List.iter (fun n -> Gamma.update g n Type.NumberType)
    [ "#pos"; "#count"; "#len"; "#next_pos"; "#lvar_375"; "#after" ];
  g

let original_core_literal units = Expr.Lit (Literal.Utf16String
  (Gillian.Utils.Utf16.of_canonical (Gillian.Utils.Utf16.of_code_units units)))

let original_finite_add_core () =
  (* Native query121; only solver-added concrete search seeds removed from
     the fixture, if present. All selected core facts remain original. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((#pos + 1.) == (#pos + 1.)))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #pos)";
      "(0. <= #count)";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
    ] in
  let expected = parse_gil_set
    [
      "(! ((#pos + 1.) == (#pos + 1.)))";
      "(is_int #pos)";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "finite_add" facts expected (original_core_gamma ());
  let counterexample = Expr.Set.add (bin ValueEqual (Expr.LVar "#pos") (Expr.num nan))
      (Expr.Set.remove (Expr.UnOp (IsInt, Expr.LVar "#pos")) expected) in
  Alcotest.(check bool) "finite_add removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let original_code_upper_core () =
  (* Native query204; only solver-added concrete search seeds removed from
     the fixture, if present. All selected core facts remain original. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(! (u16-code(#s, (num_to_int #pos)) <= 56319.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #next_pos)";
      "(is_int #pos)";
      "(is_int (#count + 1.))";
      "(0. <= #count)";
      "(0. <= (#count + 1.))";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== ((#pos + 1.) + 1.))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#count + 1.) <= #next_pos)";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
    ] in
  let expected = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (u16-code(#s, (num_to_int #pos)) <= 56319.))";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "code_upper" facts expected (original_core_gamma ());
  let counterexample = Expr.Set.union
      (parse_gil_set [ "(! (u16-code(#s, (num_to_int #pos)) <= 56319.))" ])
      (Expr.Set.of_list
         [ bin Equal (Expr.LVar "#pos") (Expr.num 0.);
           bin Equal (Expr.LVar "#s") (original_core_literal [57344]) ]) in
  Alcotest.(check bool) "code_upper removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let original_length_index_core () =
  (* Native query361; only solver-added concrete search seeds removed from
     the fixture, if present. All selected core facts remain original. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) < 56320.))";
      "(! (((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #next_pos)";
      "(is_int #pos)";
      "(is_int (#count + 1.))";
      "(0. <= #count)";
      "(0. <= (#count + 1.))";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== (#pos + 1.))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int (#pos + 1.))))";
      "((#count + 1.) <= #next_pos)";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
    ] in
  let expected = parse_gil_set
    [
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(is_int #pos)";
      "(0. <= #count)";
      "(#count <= #pos)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int (#pos + 1.))))";
      "((#pos + 1.) < #len)";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "length_index" facts expected (original_core_gamma ());
  let counterexample = let failed = bin ILessThanEqual (Expr.UnOp (Utf16Len, Expr.LVar "#s"))
      (Expr.UnOp (NumToInt, Expr.UnOp (ToIntOp,
          bin FPlus (Expr.LVar "#pos") (Expr.num 1.)))) in
    Expr.Set.union (Expr.Set.remove failed expected)
      (Expr.Set.of_list
         [ bin Equal (Expr.LVar "#pos") (Expr.num 0.);
           bin Equal (Expr.LVar "#count") (Expr.num 0.);
           bin Equal (Expr.LVar "#len") (Expr.num 2.);
           bin Equal (Expr.LVar "#s") (original_core_literal [65;65]) ]) in
  Alcotest.(check bool) "length_index removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let numeric_dependency_focus () =
  let facts = parse_gil_set
    [
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #pos)";
      "(0. <= #count)";
      "(#after <= #len)";
      "(#count <= #pos)";
      "(#len <= 9007199254740991.)";
      "(#pos < #len)";
      "((#after v== (#pos + 1.)) or (#after v== ((#pos + 1.) + 1.)))";
    ] in
  let g = original_core_gamma () in
  let goal = bin FLessThanEqual
    (bin FPlus (Expr.LVar "#count") (Expr.num 1.)) (Expr.LVar "#after") in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before = queries () and saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) "original complete numeric dependency entailment" true
      (Solver.check_entailment Utils.Containers.SS.empty
         (Engine.PFS.of_list (Expr.Set.elements facts)) [goal] g);
    let full = Expr.Set.add (not_ goal) facts in
    let lossy = parse_gil_set
      [ "(! ((#count + 1.) <= #after))"; "(is_int #count)";
        "(0. <= #count)"; "(#after <= #len)"; "(#count <= #pos)";
        "((#after v== (#pos + 1.)) or (#after v== ((#pos + 1.) + 1.)))" ] in
    let prefix fs = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) fs in
    let fresh = List.filter (fun n -> not (List.mem n before)) (queries ()) in
    let contents = List.map (fun n ->
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" n) in
      Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch))) fresh in
    Alcotest.(check bool) "complete numeric native query observed" true
      (List.exists (String.starts_with ~prefix:(prefix full)) contents);
    Alcotest.(check bool) "lossy focused query is not submitted" false
      (List.exists (String.starts_with ~prefix:(prefix lossy)) contents));
  let concrete = Expr.Set.union facts
    (parse_gil_set [ "(#pos == 0.)"; "(#count == 0.)";
                     "(#after == 1.)"; "(#len == 2.)" ]) in
  Alcotest.(check bool) "nearby stronger numeric goal retains counterexample" false
    (Solver.check_entailment Utils.Containers.SS.empty
       (Engine.PFS.of_list (Expr.Set.elements concrete))
       [bin FLessThanEqual
          (bin FPlus (Expr.LVar "#count") (Expr.num 2.)) (Expr.LVar "#after")]
       (original_core_gamma ()))


let original_mask_lower_core () =
  (* Retained native query190; only concrete search seeds removed. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (56320. <= u16-code(#s, (num_to_int (#pos + 1.)))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #next_pos)";
      "(is_int #pos)";
      "(is_int (#count + 1.))";
      "(0. <= #count)";
      "(0. <= (#count + 1.))";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== ((#pos + 1.) + 1.))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#count + 1.) <= #next_pos)";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
    ] in
  let expected = parse_gil_set
    [
      "(! (56320. <= u16-code(#s, (num_to_int (#pos + 1.)))))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "mask_lower" facts expected (original_core_gamma ());
  let counterexample = Expr.Set.union
    (parse_gil_set
    [
      "(! (56320. <= u16-code(#s, (num_to_int (#pos + 1.)))))";
    ])
    (Expr.Set.of_list
       [bin ValueEqual (Expr.LVar "#pos") (Expr.num 0.);
        bin Equal (Expr.LVar "#s") (original_core_literal [65;55296])]) in
  Alcotest.(check bool) "mask_lower removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let original_mask_upper_core () =
  (* Retained native query218; only concrete search seeds removed. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) <= 57343.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #next_pos)";
      "(is_int #pos)";
      "(is_int (#count + 1.))";
      "(0. <= #count)";
      "(0. <= (#count + 1.))";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== ((#pos + 1.) + 1.))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#count + 1.) <= #next_pos)";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
    ] in
  let expected = parse_gil_set
    [
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) <= 57343.))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.)";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "mask_upper" facts expected (original_core_gamma ());
  let counterexample = Expr.Set.union
    (parse_gil_set
    [
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) <= 57343.))";
    ])
    (Expr.Set.of_list
       [bin ValueEqual (Expr.LVar "#pos") (Expr.num 0.);
        bin Equal (Expr.LVar "#s") (original_core_literal [65;57344])]) in
  Alcotest.(check bool) "mask_upper removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let original_mask_complement_core () =
  (* Retained native query315; only concrete search seeds removed. *)
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (57343. < u16-code(#s, (num_to_int (#pos + 1.)))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! (#value == none))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#pos + 1.))))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) < 56320.))";
      "(! (((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #next_pos)";
      "(is_int #pos)";
      "(is_int (#count + 1.))";
      "(0. <= #count)";
      "(0. <= (#count + 1.))";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== (#pos + 1.))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#count + 1.) <= #next_pos)";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
    ] in
  let expected = parse_gil_set
    [
      "(! (57343. < u16-code(#s, (num_to_int (#pos + 1.)))))";
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) < 56320.))";
      "(! (((num_to_int32 u16-code(#s, (num_to_int (#pos + 1.)))) &f 64512.) == 56320.))";
    ] in
  assert (Expr.Set.subset expected facts);
  observe_original_core "mask_complement" facts expected (original_core_gamma ());
  let counterexample = Expr.Set.union
    (parse_gil_set
    [
      "(! (57343. < u16-code(#s, (num_to_int (#pos + 1.)))))";
      "(! (u16-code(#s, (num_to_int (#pos + 1.))) < 56320.))";
    ])
    (Expr.Set.of_list
       [bin ValueEqual (Expr.LVar "#pos") (Expr.num 0.);
        bin Equal (Expr.LVar "#s") (original_core_literal [65;56320])]) in
  Alcotest.(check bool) "mask_complement removed-premise counterexample is SAT" true
    (Option.is_some (Smt.check_sat counterexample
       (Gamma.as_hashtbl (original_core_gamma ()))))

let observe_length_projection label facts expected gamma =
  let g = Gamma.as_hashtbl gamma in
  let before_gamma = Hashtbl.copy g in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before = queries () and saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) (label ^ " original query is UNSAT") true
      (Option.is_none (Smt.check_sat facts g));
    let fresh = List.filter (fun name -> not (List.mem name before)) (queries ()) in
    Alcotest.(check int) (label ^ " one native projection query") 1 (List.length fresh);
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) expected in
    let ch = open_in_bin (Filename.concat "gillian_smt_queries" (List.hd fresh)) in
    let contents = Fun.protect ~finally:(fun () -> close_in ch)
      (fun () -> really_input_string ch (in_channel_length ch)) in
    Alcotest.(check bool) (label ^ " exact numeric projection observed") true
      (String.starts_with ~prefix contents);
    Alcotest.(check bool) (label ^ " caller gamma unchanged") true
      (Hashtbl.length g = Hashtbl.length before_gamma &&
       Hashtbl.fold (fun k v ok -> ok && Hashtbl.find_opt g k = Some v)
         before_gamma true);
    Printf.printf "LENGTH_PROJECTION_NATIVE_QUERY=%s:%s\n%!" label (List.hd fresh))

let original_length_projection () =
  let facts = parse_gil_set
    [
      "(! (56319. < u16-code(#s, (num_to_int #pos))))";
      "(! (#len v== -0.))";
      "(! (#pos v== -0.))";
      "(! ((num_to_int #pos) < 0.))";
      "(! ((num_to_int (#pos + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #pos)))";
      "(! (u16-code(#s, (num_to_int #pos)) < 55296.))";
      "(is_int #count)";
      "(is_int #len)";
      "(is_int #pos)";
      "(0. <= #count)";
      "(#count <= #pos)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_375 v== (9007199254740991. - #pos))";
      "(#pos == #pos)";
      "(#pos < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((as_num (u16-len #s)) <= (num_to_int (#pos + 1.)))";
      "((#pos + 1.) == (#pos + 1.))";
      "((#pos + 1.) < #len)";
      "(u16-code(#s, (num_to_int #pos)) == u16-code(#s, (num_to_int #pos)))";
    ] in
  let core = parse_gil_set
    [
      "(is_int #pos)";
      "(#len == (as_num (u16-len #s)))";
      "((as_num (u16-len #s)) <= (num_to_int (#pos + 1.)))";
      "((#pos + 1.) < #len)";
    ] in
  assert (Expr.Set.subset core facts);
  let expected name =
    let p = Expr.LVar "#pos" and n = Expr.LVar "#len" in
    let abstract = Expr.LVar name in
    let sum = bin FPlus p (Expr.num 1.) in
    Expr.Set.of_list [Expr.UnOp (IsInt,p); bin Equal n abstract;
      bin FLessThanEqual abstract (Expr.UnOp (ToIntOp,sum));
      bin FLessThan sum n] in
  observe_length_projection "plain" facts
    (expected "#utf16_length_projection_0") (original_core_gamma ());
  let occupied = original_core_gamma () in
  Gamma.update occupied "#utf16_length_projection_0" Type.StringType;
  let collision = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#utf16_length_projection_1")
       (Expr.LVar "#utf16_length_projection_1")) facts in
  observe_length_projection "collision" collision
    (expected "#utf16_length_projection_2") occupied;
  (* Each missing-selector-premise case has a real model in the original
     UTF16 domain, not merely in the wider numeric projection. *)
  List.iter
    (fun (label,removed,pos,length,units) ->
      let concrete = Expr.Set.union (Expr.Set.remove removed core)
        (Expr.Set.of_list
          [bin Equal (Expr.LVar "#pos") (Expr.num pos);
           bin Equal (Expr.LVar "#len") (Expr.num length);
           bin Equal (Expr.LVar "#s") (original_core_literal units)]) in
      Alcotest.(check bool) ("length projection missing " ^ label ^ " is SAT") true
        (Option.is_some (Smt.check_sat concrete
           (Gamma.as_hashtbl (original_core_gamma ())))))
    [ ("integrality", Expr.UnOp (IsInt,Expr.LVar "#pos"), -1.5,0.,[]);
      ("link", bin Equal (Expr.LVar "#len")
         (Expr.UnOp (IntToNum,Expr.UnOp (Utf16Len,Expr.LVar "#s"))),0.,2.,[]);
      ("failed comparison", bin FLessThanEqual
         (Expr.UnOp (IntToNum,Expr.UnOp (Utf16Len,Expr.LVar "#s")))
         (Expr.UnOp (ToIntOp,bin FPlus (Expr.LVar "#pos") (Expr.num 1.))),
         0.,2.,[65;65]) ]

(* Recorded wrong-post definedness obligations: the four-atom contained
   query dropped the length alias and returned unknown; the richer query was
   UNSAT. Observe the actual native queries, not just the returned boolean. *)
let utf16_length_alias_contained () =
  let cases = [
    ("direct", "#lvar_396", 0,
     parse_gil_set [
      "(is_int #lvar_396)";
      "(0. <= #lvar_396)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == (as_num (u16-len #s)))";
      "(#len == (#lvar_396 + 1.))";
      "(#lvar_396 < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int #lvar_396)))";
    ],
     parse_gil_set [
      "(is_int #lvar_396)";
      "(0. <= #lvar_396)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int #lvar_396)))";
    ]);
    ("next", "#lvar_402", 1,
     parse_gil_set [
      "(is_int #lvar_402)";
      "(0. <= #lvar_402)";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == (as_num (u16-len #s)))";
      "(#len == ((#lvar_402 + 1.) + 1.))";
      "(#lvar_402 < #len)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int (#lvar_402 + 1.))))";
      "((#lvar_402 + 1.) < #len)";
    ],
     parse_gil_set [
      "(is_int #lvar_402)";
      "(0. <= #lvar_402)";
      "((u16-len #s) i<= 9007199254740991i)";
      "((u16-len #s) i<= (as_int (num_to_int (#lvar_402 + 1.))))";
    ])
  ] in
  List.iter (fun (label, pname, offset, full, lossy) ->
    let s = Expr.LVar "#s" and p = Expr.LVar pname in
    let length = Expr.UnOp (Utf16Len, s) in
    let index = if offset = 0 then p else bin FPlus p (Expr.num 1.) in
    let converted = Expr.UnOp (NumToInt, Expr.UnOp (ToIntOp, index)) in
    let failed = bin ILessThanEqual length converted in
    assert (Expr.Set.mem failed full && Expr.Set.mem failed lossy);
    let irrelevant = Expr.UnOp (IsInt, Expr.LVar "#irrelevant_count") in
    let facts = Expr.Set.add irrelevant (Expr.Set.remove failed full) in
    let fresh_gamma () =
      let g = Gamma.init () in
      Gamma.update g "#s" Type.Utf16Type;
      List.iter (fun n -> Gamma.update g n Type.NumberType)
        [pname; "#len"; "#irrelevant_count"];
      g
    in
    let entail fs goal = Solver.check_entailment Utils.Containers.SS.empty
      (Engine.PFS.of_list (Expr.Set.elements fs)) [goal] (fresh_gamma ()) in
    let goal = bin ILessThan converted length in
    let queries () = if Sys.file_exists "gillian_smt_queries" then
      Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
    let prefix fs = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) fs in
    let before = queries () and saved = !Config.dump_smt in
    Config.dump_smt := true;
    Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
      Alcotest.(check bool) (label ^ " original index bound") true
        (entail facts goal);
      let fresh = List.filter (fun n -> not (List.mem n before)) (queries ()) in
      let contents = List.map (fun n ->
        let ch = open_in_bin (Filename.concat "gillian_smt_queries" n) in
        let text = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        (n,text)) fresh in
      let retained = List.filter (fun (_,text) ->
        String.starts_with ~prefix:(prefix (Expr.Set.add irrelevant full)) text) contents in
      Alcotest.(check int) (label ^ " native query retains length alias") 1
        (List.length retained);
      Alcotest.(check bool) (label ^ " lossy contained query not submitted") false
        (List.exists (fun (_,text) -> String.starts_with ~prefix:(prefix lossy) text)
           contents);
      Printf.printf "UTF16_LENGTH_ALIAS_NATIVE_QUERY=%s:%s\n%!"
        label (fst (List.hd retained)));
    let rounded = Expr.UnOp (IntToNum, length) in
    let link = bin Equal (Expr.LVar "#len") rounded in
    let value_link = bin ValueEqual (Expr.LVar "#len") rounded in
    assert (Expr.Set.mem link facts && Expr.Set.mem value_link facts);
    let concrete units = Expr.Set.of_list
      [ bin ValueEqual p (Expr.num 0.);
        bin ValueEqual (Expr.LVar "#len") (Expr.num (float_of_int (offset + 1)));
        bin Equal s (original_core_literal units) ] in
    let without_links = Expr.Set.remove link (Expr.Set.remove value_link facts) in
    Alcotest.(check bool) (label ^ " missing length aliases reject") false
      (entail (Expr.Set.union without_links (concrete [])) goal);
    let actual = concrete (List.init (offset + 1) (fun _ -> 65)) in
    let stronger = bin ILessThan
      (Expr.UnOp (NumToInt, Expr.UnOp (ToIntOp, bin FPlus index (Expr.num 1.))))
      length in
    Alcotest.(check bool) (label ^ " stronger index bound rejects") false
      (entail (Expr.Set.union facts actual) stronger)) cases

(* Captured Ucs2ZeroCount definedness obligations: focused queries 30/69/92
   returned unknown, while complete queries 31/70/93 were UNSAT. *)
let utf16_length_focused_dependencies () =
  let cases = [
    ("direct", 0, parse_gil_set [
        "(is_int #count)";
        "(is_int #pos)";
        "(is_int #zeroPrevious)";
        "(0. <= #count)";
        "(0. <= #zeroPrevious)";
        "(#count == 0.)";
        "(#count == (#zeroPreviousCount + 1.))";
        "(#count <= #pos)";
        "(#len == 0.)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == 0.)";
        "(#pos == (#zeroPrevious + 1.))";
        "(#pos <= #len)";
        "(#s == u16\"\")";
        "(#zeroPrevious == 0.)";
        "(#zeroPrevious < #pos)";
        "(#zeroPreviousCount == 0.)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int #zeroPrevious)))";
      ],
     parse_gil_set [
        "(is_int #zeroPrevious)";
        "(0. <= #zeroPrevious)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == (#zeroPrevious + 1.))";
        "(#zeroPrevious < #pos)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int #zeroPrevious)))";
      ]);
    ("terminal", 0, parse_gil_set [
        "(! ((#zeroPrevious + 1.) < #len))";
        "(is_int #count)";
        "(is_int #pos)";
        "(is_int #zeroPrevious)";
        "(0. <= #count)";
        "(0. <= #zeroPrevious)";
        "(#count == 0.)";
        "(#count == (#zeroPreviousCount + 1.))";
        "(#count <= #pos)";
        "(#len == 0.)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == 0.)";
        "(#pos == (#zeroPrevious + 1.))";
        "(#pos <= #len)";
        "(#s == u16\"\")";
        "(#zeroPrevious == 0.)";
        "(#zeroPrevious < #pos)";
        "(#zeroPreviousCount == 0.)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int #zeroPrevious)))";
      ],
     parse_gil_set [
        "(! ((#zeroPrevious + 1.) < #len))";
        "(is_int #zeroPrevious)";
        "(0. <= #zeroPrevious)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == (#zeroPrevious + 1.))";
        "(#zeroPrevious < #pos)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int #zeroPrevious)))";
      ]);
    ("next", 1, parse_gil_set [
        "(is_int #count)";
        "(is_int #pos)";
        "(is_int #zeroPrevious)";
        "(0. <= #count)";
        "(0. <= #zeroPrevious)";
        "(#count == 0.)";
        "(#count == (#zeroPreviousCount + 1.))";
        "(#count <= #pos)";
        "(#len == 0.)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == 0.)";
        "(#pos == (#zeroPrevious + 1.))";
        "(#pos <= #len)";
        "(#s == u16\"\")";
        "(#zeroPrevious == 0.)";
        "(#zeroPrevious < #pos)";
        "(#zeroPreviousCount == 0.)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int (#zeroPrevious + 1.))))";
        "((#zeroPrevious + 1.) < #len)";
      ],
     parse_gil_set [
        "(is_int #zeroPrevious)";
        "(0. <= #zeroPrevious)";
        "(#len == (as_num (u16-len #s)))";
        "(#pos == (#zeroPrevious + 1.))";
        "(#zeroPrevious < #pos)";
        "((u16-len #s) i<= 9007199254740991i)";
        "((u16-len #s) i<= (as_int (num_to_int (#zeroPrevious + 1.))))";
        "((#zeroPrevious + 1.) < #len)";
      ])
  ] in
  List.iter (fun (label, offset, full, lossy) ->
    let s = Expr.LVar "#s" and p = Expr.LVar "#zeroPrevious" in
    let length = Expr.UnOp (Utf16Len, s) in
    let index = if offset = 0 then p else bin FPlus p (Expr.num 1.) in
    let converted = Expr.UnOp (NumToInt, Expr.UnOp (ToIntOp, index)) in
    let failed = bin ILessThanEqual length converted in
    assert (Expr.Set.mem failed full && Expr.Set.subset lossy full);
    let facts = Expr.Set.remove failed full in
    let fresh_gamma () =
      let g = Gamma.init () in
      Gamma.update g "#s" Type.Utf16Type;
      List.iter (fun n -> Gamma.update g n Type.NumberType)
        ["#count"; "#pos"; "#len"; "#zeroPrevious"; "#zeroPreviousCount"];
      g
    in
    let entail fs goal = Solver.check_entailment Utils.Containers.SS.empty
      (Engine.PFS.of_list (Expr.Set.elements fs)) [goal] (fresh_gamma ()) in
    let goal = bin ILessThan converted length in
    let queries () = if Sys.file_exists "gillian_smt_queries" then
      Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
    let before = queries () and saved = !Config.dump_smt in
    Config.dump_smt := true;
    Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
      Alcotest.(check bool) (label ^ " complete contradiction proves goal") true
        (entail facts goal);
      let fresh = List.filter (fun n -> not (List.mem n before)) (queries ()) in
      let lossy_prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
        (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) lossy in
      List.iter (fun n ->
        let ch = open_in_bin (Filename.concat "gillian_smt_queries" n) in
        let text = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        Alcotest.(check bool) (label ^ " no lossy focused query") false
          (String.starts_with ~prefix:lossy_prefix text)) fresh;
      Printf.printf "UTF16_FOCUSED_LENGTH_QUERIES=%s:%d\n%!" label (List.length fresh));
    (* A satisfiable state with index equal to length must not prove index <
       length. Concrete values make this a genuine original-domain witness. *)
    let concrete = Expr.Set.of_list
      [ bin ValueEqual p (Expr.num 0.);
        bin Equal s (original_core_literal (List.init offset (fun _ -> 65))) ] in
    Alcotest.(check bool) (label ^ " false bound retains counterexample") false
      (entail concrete goal)) cases

(* Native caller rank query337. The printed bound is restored from its
   captured binary64 bits 433fffffffffffff, not rounded decimal diagnostics. *)
let simplified_rank_goal () =
  let module L = Logging in
  L.Mode.set_mode (Enabled Normal);
  L.initialize [ L.file_reporter ];
  Fun.protect ~finally:(fun () ->
    L.wrap_up (); L.initialize []; L.Mode.set_mode (Enabled Verbose))
    (fun () ->
  let facts = parse_gil_set [
      "(! (56319. < u16-code(#s, (num_to_int #lvar_463))))";
      "(! (#len v== -0.))";
      "(! (#lvar_463 v== -0.))";
      "(! (#lvar_464 == none))";
      "(! ((num_to_int #lvar_463) < 0.))";
      "(! ((num_to_int (#lvar_463 + 1.)) < 0.))";
      "(! ((as_num (u16-len #s)) <= (num_to_int #lvar_463)))";
      "(! ((as_num (u16-len #s)) <= (num_to_int (#lvar_463 + 1.))))";
      "(! (u16-code(#s, (num_to_int #lvar_463)) < 55296.))";
      "(is_int #len)";
      "(is_int #lvar_462)";
      "(is_int #lvar_463)";
      "(is_int #next_pos)";
      "(is_int (#lvar_462 + 1.))";
      "(0. <= #lvar_462)";
      "(0. <= (#lvar_462 + 1.))";
      "(#len v== (as_num (u16-len #s)))";
      "(#len == #len)";
      "(#len == (as_num (u16-len #s)))";
      "(#len <= 9007199254740991.)";
      "(#lvar_461 v== (9007199254740991. - #lvar_463))";
      "(#lvar_462 <= #lvar_463)";
      "(#lvar_463 == #lvar_463)";
      "(#lvar_463 < #len)";
      "(#lvar_js_13 v== #lvar_js_21)";
      "(#lvar_js_13 v== #lvar_js_25)";
      "(#lvar_js_14 v== #lvar_js_22)";
      "(#lvar_js_14 v== #lvar_js_26)";
      "(#lvar_js_15 v== #lvar_js_23)";
      "(#lvar_js_15 v== #lvar_js_27)";
      "(#lvar_js_21 v== #lvar_js_13)";
      "(#lvar_js_22 v== #lvar_js_14)";
      "(#lvar_js_23 v== #lvar_js_15)";
      "(#lvar_js_25 v== #lvar_js_13)";
      "(#lvar_js_26 v== #lvar_js_14)";
      "(#lvar_js_27 v== #lvar_js_15)";
      "(#next_pos v== ((#lvar_463 + 1.) + 1.))";
      "((u16-len #s) i<= 9007199254740991i)";
      "((#lvar_462 + 1.) <= #next_pos)";
      "((#lvar_463 + 1.) == (#lvar_463 + 1.))";
      "((#lvar_463 + 1.) < #len)";
      "(u16-code(#s, (num_to_int #lvar_463)) == u16-code(#s, (num_to_int #lvar_463)))";
      "(((num_to_int32 u16-code(#s, (num_to_int (#lvar_463 + 1.)))) &f 64512.) == 56320.)";
  ] in
  let gamma () =
    let g = Gamma.init () in
    Gamma.update g "#s" Type.Utf16Type;
    List.iter (fun n -> Gamma.update g n Type.NumberType)
      [ "#len"; "#lvar_461"; "#lvar_462"; "#lvar_463"; "#next_pos" ];
    g
  in
  let rank = bin FMinus (Expr.num 9007199254740991.) (Expr.LVar "#next_pos") in
  let goals = [ Expr.UnOp (IsInt, rank);
                bin FLessThanEqual (Expr.num 0.) rank;
                bin FLessThan rank (Expr.LVar "#lvar_461") ] in
  let before = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) "captured rank conjunction is proved" true
      (Solver.check_entailment Utils.Containers.SS.empty
         (Engine.PFS.of_list (Expr.Set.elements facts)) goals (gamma ()));
    let fresh = Array.to_list (Sys.readdir "gillian_smt_queries")
      |> List.filter (fun n -> not (List.mem n before)) in
    Printf.printf "NORMALIZED_RANK_QUERIES=%d\n%!" (List.length fresh);
    Alcotest.(check bool) "rank proof used actual native queries" true
      (List.length fresh > 0));
  (* Removing the true rank claims cannot let an unrelated false conjunct
     pass: a concrete numeric state supplies a satisfiable counterexample. *)
  let concrete = parse_gil_set [
    "(#lvar_463 v== 0.)"; "(#len v== 2.)";
    "(#next_pos v== 2.)"; "(#lvar_461 v== 9007199254740991.)" ] in
  Alcotest.(check bool) "false rank conjunct remains rejected" false
    (Solver.check_entailment Utils.Containers.SS.empty
       (Engine.PFS.of_list (Expr.Set.elements concrete))
       [bin FLessThanEqual (Expr.LVar "#lvar_461") rank] (gamma ()));
  let ch = open_in_bin "file.log" in
  let log = Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch)) in
  Alcotest.(check bool) "rank checks have no SMT unknown" false
    (List.mem "The solver returned: unknown" (String.split_on_char '\n' log)))

let check_array_counter_witness ?(fixed = []) zero label facts gamma =
  let g = Gamma.as_hashtbl gamma in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before = queries () and saved = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved) (fun () ->
    Alcotest.(check bool) "complete array feasibility has a native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let seed = Expr.Set.add
        (bin ValueEqual (Expr.LVar "#index") (Expr.num (if zero then 0. else 1.)))
        (Expr.Set.add (bin Equal (Expr.UnOp (Utf16Len, Expr.LVar "#confidence"))
          (Expr.int 1)) facts) in
    let seed = List.fold_left (fun fs (name, value) -> Expr.Set.add
        (bin ValueEqual (Expr.LVar name) (Expr.num value)) fs) seed fixed in
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let fresh = List.filter (fun n -> not (List.mem n before)) (queries ()) in
    let observed = List.filter (fun name ->
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) fresh in
    Alcotest.(check int) "native witness retains every original assertion" 1
      (List.length observed);
    Printf.printf "ARRAY_STEP_NATIVE_QUERY=%s:%s\n%!"
      label (List.hd observed));
  let impossible = Expr.Set.add
      (bin ValueEqual (Expr.LVar "#failingLen") (Expr.num 0.)) facts in
  Alcotest.(check bool) "complete contradictory query remains UNSAT" true
    (Option.is_none (Smt.check_sat impossible g))

let array_counter_witness zero () =
  (* Complete feasibility query from the original AJV string-array loop.
     No assumptions are removed; the seed is only a native model search. *)
  let facts = parse_gil_set [
    "(! (#key == none))";
    "(! (#lvar_464 < 1.))";
    "(! (#lvar_473 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_473)";
    "(is_int (4294967295. - (#index + 1.)))";
    "(is_int (#index + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #before))";
    "(0i i<= (l-len #tail))";
    "(0. < #index)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_473)";
    "(0. <= (4294967295. - (#index + 1.)))";
    "(0. <= (#index + 1.))";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == #index)";
    "(#index < #failingLen)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_175)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_176)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_178)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_179)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_175 v== #lvar_142)";
    "(#lvar_176 v== #lvar_143)";
    "(#lvar_178 v== #lvar_145)";
    "(#lvar_179 v== #lvar_146)";
    "(#lvar_473 == #lvar_473)";
    "(#lvar_473 <= (as_num (u16-len #confidence)))";
    "(#lvar_477 v== (4294967295. - #index))";
    "(#lvar_478 v== #item)";
    "(#lvar_479 v== #tail)";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_17 v== #lvar_js_45)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_18 v== #lvar_js_46)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#lvar_js_45 v== #lvar_js_17)";
    "(#lvar_js_46 v== #lvar_js_18)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #item) i<= 9007199254740991i)";
    "((u16-len #previous) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((4294967295. - (#index + 1.)) < (4294967295. - #index))";
    "((#index + 1.) <= 4294967295.)";
    "((#lvar_464 == 0.) or (#lvar_464 == 1.))";
    "(((#index + 1.) - 1.) == #index)";
    "(((#lvar_464 == 0.) and (#key == undefined)) or ((#lvar_464 == 1.) and (#key == u16\"classification\")))";
    "(((#lvar_473 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_473) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = if not zero then facts else
    let remove = parse_gil_set ["(0. < #index)";
      "(0i i<= (l-len #before))";
      "((u16-len #previous) i<= 9007199254740991i)"] in
    let add = parse_gil_set ["(! (0. < #index))";
      "(0. <= #index)"; "(#index == 0.)"] in
    Expr.Set.union add (Expr.Set.diff facts remove) in
  let gamma = Gamma.init () in
  Gamma.update gamma "#lvar_477" Type.NumberType;
  Gamma.update gamma "#before" Type.ListType;
  Gamma.update gamma "#previous" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#tail" Type.ListType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#item" Type.Utf16Type;
  Gamma.update gamma "#lvar_464" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_473" Type.NumberType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  if zero then List.iter (Gamma.remove gamma) ["#before"; "#previous"];
  check_array_counter_witness zero (if zero then "zero" else "positive") facts gamma

let array_predecessor_witness () =
  (* Complete captured feasibility query after the checked prefix inverse. *)
  let facts = parse_gil_set [
    "(! (#key == none))";
    "(! (#lvar_466 < 1.))";
    "(! (#lvar_475 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_475)";
    "(is_int (#index - 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #before))";
    "(0i i<= (l-len #lvar_481))";
    "(0i i<= (l-len #tail))";
    "(0. < #index)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_475)";
    "(0. <= (#index - 1.))";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == #index)";
    "(#index < #failingLen)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_175)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_176)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_178)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_179)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_175 v== #lvar_142)";
    "(#lvar_176 v== #lvar_143)";
    "(#lvar_178 v== #lvar_145)";
    "(#lvar_179 v== #lvar_146)";
    "(#lvar_475 == #lvar_475)";
    "(#lvar_475 <= (as_num (u16-len #confidence)))";
    "(#lvar_479 v== (4294967295. - #index))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_17 v== #lvar_js_45)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_18 v== #lvar_js_46)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#lvar_js_45 v== #lvar_js_17)";
    "(#lvar_js_46 v== #lvar_js_18)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #lvar_480) i<= 9007199254740991i)";
    "((u16-len #previous) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((#index - 1.) < 4294967295.)";
    "((#lvar_466 == 0.) or (#lvar_466 == 1.))";
    "(((#index - 1.) + 1.) == #index)";
    "(((#lvar_466 == 0.) and (#key == undefined)) or ((#lvar_466 == 1.) and (#key == u16\"classification\")))";
    "(((#lvar_475 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_475) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let gamma = Gamma.init () in
  Gamma.update gamma "#lvar_479" Type.NumberType;
  Gamma.update gamma "#before" Type.ListType;
  Gamma.update gamma "#previous" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_475" Type.NumberType;
  Gamma.update gamma "#tail" Type.ListType;
  Gamma.update gamma "#lvar_480" Type.Utf16Type;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#lvar_466" Type.NumberType;
  Gamma.update gamma "#item" Type.Utf16Type;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#lvar_481" Type.ListType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  check_array_counter_witness false "predecessor" facts gamma

let independent_array_counters () =
  (* Complete target-loop query: the earlier index is positive, target index zero. *)
  let facts = parse_gil_set [
    "(! (0. < #targetIndex))";
    "(! (#index < #failingLen))";
    "(! (#key == none))";
    "(! (#lvar_468 < 1.))";
    "(! (#lvar_477 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_477)";
    "(is_int #targetIndex)";
    "(is_int #targetLen)";
    "(is_int (4294967295. - (#targetIndex + 1.)))";
    "(is_int (#index - 1.))";
    "(is_int (#targetIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #before))";
    "(0i i<= (l-len #targetTail))";
    "(0. < #index)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_477)";
    "(0. <= #targetIndex)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#targetIndex + 1.)))";
    "(0. <= (#index - 1.))";
    "(0. <= (#targetIndex + 1.))";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == #failingLen)";
    "(#index == #index)";
    "(#index <= #failingLen)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_175)";
    "(#lvar_142 v== #lvar_575)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_176)";
    "(#lvar_143 v== #lvar_576)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_178)";
    "(#lvar_145 v== #lvar_578)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_179)";
    "(#lvar_146 v== #lvar_579)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_175 v== #lvar_142)";
    "(#lvar_176 v== #lvar_143)";
    "(#lvar_178 v== #lvar_145)";
    "(#lvar_179 v== #lvar_146)";
    "(#lvar_477 == #lvar_477)";
    "(#lvar_477 <= (as_num (u16-len #confidence)))";
    "(#lvar_481 v== (4294967295. - #index))";
    "(#lvar_587 v== (4294967295. - #targetIndex))";
    "(#lvar_588 v== #targetItem)";
    "(#lvar_589 v== #targetTail)";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_17 v== #lvar_js_45)";
    "(#lvar_js_17 v== #lvar_js_53)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_18 v== #lvar_js_46)";
    "(#lvar_js_18 v== #lvar_js_54)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#lvar_js_45 v== #lvar_js_17)";
    "(#lvar_js_46 v== #lvar_js_18)";
    "(#lvar_js_53 v== #lvar_js_17)";
    "(#lvar_js_54 v== #lvar_js_18)";
    "(#targetIndex == 0.)";
    "(#targetIndex == #targetIndex)";
    "(#targetIndex < #targetLen)";
    "(#targetLen == #targetLen)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #previous) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((u16-len #targetItem) i<= 9007199254740991i)";
    "((4294967295. - (#targetIndex + 1.)) < (4294967295. - #targetIndex))";
    "((#index - 1.) < 4294967295.)";
    "((#lvar_468 == 0.) or (#lvar_468 == 1.))";
    "((#targetIndex + 1.) <= 4294967295.)";
    "(((#index - 1.) + 1.) == #index)";
    "(((#lvar_468 == 0.) and (#key == undefined)) or ((#lvar_468 == 1.) and (#key == u16\"classification\")))";
    "(((#lvar_477 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_477) and (0. < (as_num (u16-len #confidence)))))";
    "(((#targetIndex + 1.) - 1.) == #targetIndex)";
  ] in
  let gamma = Gamma.init () in
  Gamma.update gamma "#targetIndex" Type.NumberType;
  Gamma.update gamma "#lvar_477" Type.NumberType;
  Gamma.update gamma "#before" Type.ListType;
  Gamma.update gamma "#lvar_580" Type.ObjectType;
  Gamma.update gamma "#previous" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_468" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#targetItem" Type.Utf16Type;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#lvar_587" Type.NumberType;
  Gamma.update gamma "#lvar_581" Type.ObjectType;
  Gamma.update gamma "#targetTail" Type.ListType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#lvar_481" Type.NumberType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  check_array_counter_witness ~fixed:[("#targetIndex", 0.)] false "independent" facts gamma

let carried_counter_witness () =
  (* Complete captured evidence-loop feasibility query, including the original
     aliases, numeric constraints and UTF16 facts. The model guess is optional. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == (#lvar_518 + 1.))";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 <= (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  (* The dump prints both EList [] and literal LList [] as {{ }}. Rebuild
     this node as EList [], matching the captured native seq.empty encoding. *)
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_519" Type.NumberType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_518" Type.NumberType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before_facts = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "optional carried-counter seed has a native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
      (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "AA")))) facts in
    let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
      (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
      [ ("#lvar_518", 0.); ("#lvar_517", 1.); ("#lvar_480", 1.);
        ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.);
        ("#evidenceLen", 1.); ("#lvar_516", 1.); ("#lvar_489", 2.) ] in
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "native witness includes every captured assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "SAT seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "CARRIED_COUNTER_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "original facts unchanged" true
    (before_facts = Expr.Set.elements facts);
  Alcotest.(check bool) "original gamma unchanged" true
    (before_gamma = gamma_entries ());
  let impossible = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#evidenceLen") (Expr.num 0.)) facts in
  Alcotest.(check bool) "contradictory complete query has no witness" true
    (Option.is_none (Smt.check_sat impossible g))

let singleton_surrogate_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(! ((#lvar_517 + 1.) < (as_num (u16-len #confidence))))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_517)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(55296. <= u16-code(#confidence, (num_to_int #lvar_517)))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == 0.)";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 == 0.)";
    "(#lvar_517 < (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((as_num (u16-len #confidence)) == (#lvar_517 + 1.))";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "(u16-code(#confidence, (num_to_int #lvar_517)) <= 56319.)";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical
    (Gillian.Utils.Utf16.of_code_units [0xd800]) in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.);
      ("#lvar_516", 0.); ("#lvar_517", 0.); ("#evidenceLen", 1.);
      ("#lvar_489", 1.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete singleton-surrogate query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "singleton native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "singleton seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "SINGLETON_SURROGATE_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "singleton facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "singleton gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "A")))) seed in
  Alcotest.(check bool) "ASCII witness cannot satisfy high-surrogate query" true
    (Option.is_none (Smt.check_sat wrong g))

let fixed_pair_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_517)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == 0.)";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 == 0.)";
    "(#lvar_517 < (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((as_num (u16-len #confidence)) == ((#lvar_517 + 1.) + 1.))";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "((#lvar_517 + 1.) < (as_num (u16-len #confidence)))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical "AA" in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.);
      ("#lvar_516", 0.); ("#lvar_517", 0.); ("#evidenceLen", 1.);
      ("#lvar_489", 1.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete fixed-pair query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    (* Multiple search shapes may submit the same complete witness. Require
       its actual native submission; duplicate submissions add no proof. *)
    Alcotest.(check bool) "fixed pair native query retains every original assertion" true
      (List.length observed >= 1);
    (* Query counts depend on cache hits and overlapping witness shapes.
       Check the actual required fallback was not submitted, rather than
       treating a count as a proof-phase signal. *)
    let original_prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) facts in
    let submitted_original = queries () |> List.exists (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix:original_prefix text) in
    Alcotest.(check bool) "fixed pair seed returns before required fallback" false
      submitted_original;
    Printf.printf "FIXED_PAIR_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "fixed pair facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "fixed pair gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "A")))) seed in
  Alcotest.(check bool) "single-unit witness cannot satisfy two-unit query" true
    (Option.is_none (Smt.check_sat wrong g))

let paired_surrogate_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_517)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(55296. <= u16-code(#confidence, (num_to_int #lvar_517)))";
    "(56320. <= u16-code(#confidence, (num_to_int (#lvar_517 + 1.))))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == 0.)";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 == 0.)";
    "(#lvar_517 < (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((as_num (u16-len #confidence)) == ((#lvar_517 + 1.) + 1.))";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "(u16-code(#confidence, (num_to_int #lvar_517)) <= 56319.)";
    "(u16-code(#confidence, (num_to_int (#lvar_517 + 1.))) <= 57343.)";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "((#lvar_517 + 1.) < (as_num (u16-len #confidence)))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical (Gillian.Utils.Utf16.of_code_units [0xd800; 0xdc00]) in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.);
      ("#lvar_516", 0.); ("#lvar_517", 0.); ("#evidenceLen", 1.);
      ("#lvar_489", 1.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete paired-surrogate query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "paired surrogate native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "paired surrogate seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "PAIRED_SURROGATE_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "paired surrogate facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "paired surrogate gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "AA")))) seed in
  Alcotest.(check bool) "ASCII pair cannot satisfy surrogate bounds" true
    (Option.is_none (Smt.check_sat wrong g))


let ordinary_singleton_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_517)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == 0.)";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 == 0.)";
    "(#lvar_517 < (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((as_num (u16-len #confidence)) == (#lvar_517 + 1.))";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "((u16-code(#confidence, (num_to_int #lvar_517)) < 55296.) or (56319. < u16-code(#confidence, (num_to_int #lvar_517))))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical "A" in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.);
      ("#lvar_516", 0.); ("#lvar_517", 0.); ("#evidenceLen", 1.);
      ("#lvar_489", 1.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete ordinary-singleton query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "ordinary singleton native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "ordinary singleton seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "ORDINARY_SINGLETON_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "ordinary singleton facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "ordinary singleton gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical (Gillian.Utils.Utf16.of_code_units [0xd800]))))) seed in
  Alcotest.(check bool) "high surrogate cannot satisfy ordinary-unit query" true
    (Option.is_none (Smt.check_sat wrong g))


let carried_bounds_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #lvar_518)";
    "(is_int #lvar_519)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_518)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == (#lvar_518 + 1.))";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 <= (as_num (u16-len #confidence)))";
    "(#lvar_518 == (#lvar_520 + 1.))";
    "(#lvar_518 <= #lvar_519)";
    "(#lvar_519 <= (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_519" Type.NumberType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_520" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#lvar_521" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_518" Type.NumberType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical "AAA" in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.); ("#lvar_520", 0.); ("#lvar_518", 1.); ("#lvar_519", 1.); ("#lvar_516", 2.); ("#lvar_517", 2.); ("#evidenceLen", 1.); ("#lvar_489", 3.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete carried-bounds query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "carried bounds native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "carried bounds seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "CARRIED_BOUNDS_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "carried bounds facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "carried bounds gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "AA")))) seed in
  Alcotest.(check bool) "short string cannot satisfy carried count" true
    (Option.is_none (Smt.check_sat wrong g))


let fixed_chain_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #lvar_516)";
    "(is_int #lvar_517)";
    "(is_int #lvar_518)";
    "(is_int #lvar_519)";
    "(is_int #targetLen)";
    "(is_int (as_num (u16-len #confidence)))";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(0i i< (u16-len #confidence))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #lvar_516)";
    "(0. <= #lvar_518)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_501)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_502)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_504)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_505)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 == (#lvar_516 + 1.))";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_516 == (#lvar_518 + 1.))";
    "(#lvar_516 <= #lvar_517)";
    "(#lvar_517 <= (as_num (u16-len #confidence)))";
    "(#lvar_518 == 0.)";
    "(#lvar_518 <= #lvar_519)";
    "(#lvar_519 == 0.)";
    "(#lvar_519 <= (as_num (u16-len #confidence)))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_506" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_519" Type.NumberType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#lvar_516" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_518" Type.NumberType;
  Gamma.update gamma "#lvar_517" Type.NumberType;
  Gamma.update gamma "#lvar_507" Type.ObjectType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical "AA" in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 0.); ("#failingLen", 0.); ("#targetLen", 0.); ("#lvar_518", 0.); ("#lvar_519", 0.); ("#lvar_516", 1.); ("#lvar_517", 1.); ("#evidenceLen", 1.); ("#lvar_489", 2.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete fixed-chain query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "fixed chain native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "fixed chain seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "FIXED_CHAIN_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "fixed chain facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "fixed chain gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "A")))) seed in
  Alcotest.(check bool) "short string cannot satisfy fixed count" true
    (Option.is_none (Smt.check_sat wrong g))


let bounded_counter_witness () =
  (* Complete captured last-unit query, without dropping aliases or contents. *)
  let facts = parse_gil_set [
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #lvar_489)";
    "(is_int #targetLen)";
    "(is_int (4294967295. - (#evidenceIndex + 1.)))";
    "(is_int (#evidenceIndex + 1.))";
    "(is_int (#evidenceIndex - 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #evidenceBefore))";
    "(0i i<= (l-len #lvar_744))";
    "(0i i<= (l-len #lvar_765))";
    "(0. == #failingLen)";
    "(0. == #targetLen)";
    "(0. < #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_489)";
    "(0. <= #targetLen)";
    "(0. <= (4294967295. - (#evidenceIndex + 1.)))";
    "(0. <= (#evidenceIndex + 1.))";
    "(0. <= (#evidenceIndex - 1.))";
    "(1. < #evidenceIndex)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex < #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen <= 4294967295.)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_142 v== #lvar_748)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_143 v== #lvar_749)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_145 v== #lvar_751)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_146 v== #lvar_752)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#targetLen <= 4294967295.)";
    "((l-len #evidenceBefore) == (l-len #lvar_744))";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((4294967295. - (#evidenceIndex + 1.)) < (4294967295. - #evidenceIndex))";
    "((#evidenceIndex + 1.) == #evidenceLen)";
    "((#evidenceIndex + 1.) <= 4294967295.)";
    "((#evidenceIndex - 1.) < 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#evidenceIndex + 1.) - 1.) == #evidenceIndex)";
    "(((#evidenceIndex - 1.) + 1.) == #evidenceIndex)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
    "(l+ (#evidenceBefore, {{ {{ #loc_193, #loc_192 }} }}) == l+ ({{ {{ #loc_223,\n                                                             #loc_222 }} }},\n                                                             #lvar_744))";
  ] in
  let facts = Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_494") (Expr.EList [])) facts in
  let locations = object
    inherit [_] Visitors.endo as super
    method! visit_expr () e = match e with
      | Expr.LVar name when String.starts_with ~prefix:"#loc_" name -> Expr.ALoc name
      | _ -> super#visit_expr () e
  end in
  let facts = Expr.Set.fold (fun e acc -> Expr.Set.add
    (locations#visit_expr () e) acc) facts Expr.Set.empty in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_763" Type.ObjectType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_765" Type.ListType;
  Gamma.update gamma "#lvar_753" Type.ObjectType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_754" Type.ObjectType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#evidenceBefore" Type.ListType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_764" Type.ObjectType;
  Gamma.update gamma "#lvar_744" Type.ListType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let gamma_entries () = Hashtbl.fold (fun n t acc -> (n, t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_gamma = gamma_entries () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  let value = Gillian.Utils.Utf16.of_canonical "A" in
  let seed = Expr.Set.add (bin Equal (Expr.LVar "#confidence")
    (Expr.Lit (Utf16String value))) facts in
  let seed = List.fold_left (fun acc (n, v) -> Expr.Set.add
    (bin ValueEqual (Expr.LVar n) (Expr.num v)) acc) seed
    [ ("#evidenceIndex", 2.); ("#failingLen", 0.); ("#targetLen", 0.); ("#evidenceLen", 3.); ("#lvar_489", 1.); ("#lvar_480", 1.) ] in
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete bounded-counter query has native SAT model" true
      (Option.is_some (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seed in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let text = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix text) in
    Alcotest.(check int) "bounded counter native query retains every original assertion" 1
      (List.length observed);
    (* Cached prechecks need not emit another native query. The exact
       complete witness above is still required once, without fallback. *)
    let count = List.length
      (List.filter (fun n -> not (List.mem n before_queries)) (queries ())) in
    Alcotest.(check bool) "bounded counter seed returns before required fallback" true
      (count >= 1 && count <= 3);
    Printf.printf "BOUNDED_COUNTER_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "bounded counter facts unchanged" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "bounded counter gamma unchanged" true
    (before_gamma = gamma_entries ());
  let wrong = Expr.Set.add (bin ValueEqual (Expr.LVar "#evidenceIndex")
    (Expr.num 1.)) seed in
  Alcotest.(check bool) "one cannot satisfy the strict lower counter bound" true
    (Option.is_none (Smt.check_sat wrong g))


let rank_case_split () =
  let facts = parse_gil_set [
    "(! (56319. < u16-code(#s, (num_to_int #lvar_434))))";
    "(! (#len v== -0.))";
    "(! (#lvar_434 v== -0.))";
    "(! (#lvar_435 == none))";
    "(! ((num_to_int #lvar_434) < 0.))";
    "(! ((num_to_int (#lvar_434 + 1.)) < 0.))";
    "(! ((as_num (u16-len #s)) <= (num_to_int #lvar_434)))";
    "(! ((as_num (u16-len #s)) <= (num_to_int (#lvar_434 + 1.))))";
    "(! (u16-code(#s, (num_to_int #lvar_434)) < 55296.))";
    "(is_int #len)";
    "(is_int #lvar_433)";
    "(is_int #lvar_434)";
    "(is_int #next_pos)";
    "(is_int (#lvar_433 + 1.))";
    "(0. <= #lvar_433)";
    "(0. <= (#lvar_433 + 1.))";
    "(#len v== (as_num (u16-len #s)))";
    "(#len == #len)";
    "(#len == (as_num (u16-len #s)))";
    "(#len <= 9007199254740991.)";
    "(#lvar_432 v== (9007199254740991. - #lvar_434))";
    "(#lvar_433 <= #lvar_434)";
    "(#lvar_434 == #lvar_434)";
    "(#lvar_434 < #len)";
    "(#lvar_js_13 v== #lvar_js_21)";
    "(#lvar_js_13 v== #lvar_js_25)";
    "(#lvar_js_14 v== #lvar_js_22)";
    "(#lvar_js_14 v== #lvar_js_26)";
    "(#lvar_js_15 v== #lvar_js_23)";
    "(#lvar_js_15 v== #lvar_js_27)";
    "(#lvar_js_21 v== #lvar_js_13)";
    "(#lvar_js_22 v== #lvar_js_14)";
    "(#lvar_js_23 v== #lvar_js_15)";
    "(#lvar_js_25 v== #lvar_js_13)";
    "(#lvar_js_26 v== #lvar_js_14)";
    "(#lvar_js_27 v== #lvar_js_15)";
    "(#next_pos v== ((#lvar_434 + 1.) + 1.))";
    "((u16-len #s) i<= 9007199254740991i)";
    "((#lvar_433 + 1.) <= #next_pos)";
    "((#lvar_434 + 1.) == (#lvar_434 + 1.))";
    "((#lvar_434 + 1.) < #len)";
    "(u16-code(#s, (num_to_int #lvar_434)) == u16-code(#s, (num_to_int #lvar_434)))";
    "(((! (is_int (9007199254740991. - #next_pos))) or (! (0. <= (9007199254740991. - #next_pos)))) or (! ((9007199254740991. - #next_pos) < #lvar_432)))";
    "(((num_to_int32 u16-code(#s, (num_to_int (#lvar_434 + 1.)))) &f 64512.) == 56320.)";
  ] in
  let gamma = Gamma.init () in
  Gamma.update gamma "#s" Type.Utf16Type;
  Gamma.update gamma "#len" Type.NumberType;
  Gamma.update gamma "#lvar_433" Type.NumberType;
  Gamma.update gamma "#lvar_434" Type.NumberType;
  Gamma.update gamma "#lvar_432" Type.NumberType;
  Gamma.update gamma "#next_pos" Type.NumberType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let types () = Hashtbl.fold (fun n t acc -> (n,t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_types = types () in
  let premises = parse_gil_set [
    "(! (#len v== -0.))";
    "(! (#lvar_434 v== -0.))";
    "(is_int #len)";
    "(is_int #lvar_433)";
    "(is_int #lvar_434)";
    "(is_int #next_pos)";
    "(is_int (#lvar_433 + 1.))";
    "(0. <= #lvar_433)";
    "(0. <= (#lvar_433 + 1.))";
    "(#len == #len)";
    "(#len <= 9007199254740991.)";
    "(#lvar_432 v== (9007199254740991. - #lvar_434))";
    "(#lvar_433 <= #lvar_434)";
    "(#lvar_434 == #lvar_434)";
    "(#lvar_434 < #len)";
    "(#next_pos v== ((#lvar_434 + 1.) + 1.))";
    "((#lvar_433 + 1.) <= #next_pos)";
    "((#lvar_434 + 1.) == (#lvar_434 + 1.))";
    "((#lvar_434 + 1.) < #len)";
  ] in
  let failed = [
    Expr.Set.choose (parse_gil_set [ "(! (is_int (9007199254740991. - #next_pos)))" ]);
    Expr.Set.choose (parse_gil_set [ "(! (0. <= (9007199254740991. - #next_pos)))" ]);
    Expr.Set.choose (parse_gil_set [ "(! ((9007199254740991. - #next_pos) < #lvar_432))" ]);
  ] in
  let cases = List.map (fun failed -> Expr.Set.add failed premises) failed in
  Alcotest.(check bool) "numeric premises belong to original query" true
    (Expr.Set.subset premises facts);
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "captured rank failure is impossible" true
      (Option.is_none (Smt.check_sat facts g));
    List.iteri (fun index branch ->
      let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
        (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) branch in
      let observed = queries () |> List.filter (fun name ->
        if List.mem name before_queries then false else
        let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
        let content = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        String.starts_with ~prefix content) in
      Alcotest.(check bool) "every rank branch has real native proof" true
        (observed <> []);
      Printf.printf "RANK_BRANCH_NATIVE_QUERY=%d:%s\n%!" index (List.hd observed)) cases);
  Alcotest.(check bool) "rank facts unchanged" true (before = Expr.Set.elements facts);
  Alcotest.(check bool) "rank gamma unchanged" true (before_types = types ());
  let bound = bin FLessThanEqual (Expr.LVar "#len") (Expr.num 9007199254740991.) in
  Alcotest.(check bool) "captured maximum bound is original" true
    (Expr.Set.mem bound facts);
  let weak_cases = List.map (Expr.Set.remove bound) cases in
  Alcotest.(check bool) "missing maximum cannot prove all rank cases" false
    (List.for_all (fun branch -> Smt.proves_unsat branch g) weak_cases);
  let descent = List.nth weak_cases 2 in
  Alcotest.(check bool) "missing maximum has native binary64 counterexample" true
    (Option.is_some (Smt.exec_sat descent g))

let list_prefix_restore () =
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (0. < #index))";
    "(! (#evidenceIndex < #evidenceLen))";
    "(! (#index < #failingLen))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(! ({{ #lvar_1023, #lvar_1109,\n   #lvar_1211 }} == l+ (l-sub(l+ (#targetBefore, {{ #targetPrevious,\n                                  #targetItem }}, #targetTail), 0i, (3i i+ (-1i i* (l-len #targetTail)))),\n                        #targetTail)))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_1348)";
    "(is_int #lvar_489)";
    "(is_int (4294967295. - (#lvar_1348 + 1.)))";
    "(is_int (#lvar_1348 + 1.))";
    "(is_int (#lvar_1348 - 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #targetBefore))";
    "(0i i<= (l-len #targetTail))";
    "(0. == #failingLen)";
    "(0. < #lvar_1348)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #index)";
    "(0. <= #lvar_489)";
    "(0. <= (4294967295. - (#lvar_1348 + 1.)))";
    "(0. <= (#lvar_1348 + 1.))";
    "(0. <= (#lvar_1348 - 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex == #evidenceLen)";
    "(#evidenceIndex <= #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == 0.)";
    "(#index == #failingLen)";
    "(#index == #index)";
    "(#index <= #failingLen)";
    "(#lvar_1024 v== {{ #lvar_1109,\n#lvar_1211 }})";
    "(#lvar_1110 v== {{ #lvar_1211 }})";
    "(#lvar_1324 v== (4294967295. - #index))";
    "(#lvar_1339 v== (4294967295. - #lvar_1348))";
    "(#lvar_1340 v== #targetItem)";
    "(#lvar_1341 v== #targetTail)";
    "(#lvar_1348 == #lvar_1348)";
    "(#lvar_1348 < 3.)";
    "(#lvar_142 v== #lvar_1010)";
    "(#lvar_142 v== #lvar_1327)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_143 v== #lvar_1011)";
    "(#lvar_143 v== #lvar_1328)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_145 v== #lvar_1013)";
    "(#lvar_145 v== #lvar_1330)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_146 v== #lvar_1014)";
    "(#lvar_146 v== #lvar_1331)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_17 v== #lvar_js_45)";
    "(#lvar_js_17 v== #lvar_js_53)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_18 v== #lvar_js_46)";
    "(#lvar_js_18 v== #lvar_js_54)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#lvar_js_45 v== #lvar_js_17)";
    "(#lvar_js_46 v== #lvar_js_18)";
    "(#lvar_js_53 v== #lvar_js_17)";
    "(#lvar_js_54 v== #lvar_js_18)";
    "((u16-len #confidence) == 1i)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #lvar_1023) i<= 9007199254740991i)";
    "((u16-len #lvar_1109) i<= 9007199254740991i)";
    "((u16-len #lvar_1211) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((u16-len #targetItem) i<= 9007199254740991i)";
    "((u16-len #targetPrevious) i<= 9007199254740991i)";
    "((4294967295. - (#lvar_1348 + 1.)) < (4294967295. - #lvar_1348))";
    "((#lvar_1348 + 1.) <= 4294967295.)";
    "((#lvar_1348 - 1.) < 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#lvar_1348 + 1.) - 1.) == #lvar_1348)";
    "(((#lvar_1348 - 1.) + 1.) == #lvar_1348)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
    "({{ #lvar_1023, #lvar_1109,\n#lvar_1211 }} == l+ (#targetBefore, {{ #targetPrevious, #targetItem }},\n                     #targetTail))";
  ] |> Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_1212") (Expr.EList [])) in
  let gamma = Gamma.init () in
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#lvar_1339" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_1109" Type.Utf16Type;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_1023" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_1324" Type.NumberType;
  Gamma.update gamma "#lvar_1348" Type.NumberType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_1211" Type.Utf16Type;
  Gamma.update gamma "#targetItem" Type.Utf16Type;
  Gamma.update gamma "#targetBefore" Type.ListType;
  Gamma.update gamma "#targetTail" Type.ListType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#targetPrevious" Type.Utf16Type;
  let g = Gamma.as_hashtbl gamma in
  let failed = Expr.Set.choose (parse_gil_set [ "(! ({{ #lvar_1023, #lvar_1109,\n   #lvar_1211 }} == l+ (l-sub(l+ (#targetBefore, {{ #targetPrevious,\n                                  #targetItem }}, #targetTail), 0i, (3i i+ (-1i i* (l-len #targetTail)))),\n                        #targetTail)))" ]) in
  let link = Expr.Set.choose (parse_gil_set [ "({{ #lvar_1023, #lvar_1109,\n#lvar_1211 }} == l+ (#targetBefore, {{ #targetPrevious, #targetItem }},\n                     #targetTail))" ]) in
  let selected = Expr.Set.of_list [ failed; link ] in
  Alcotest.(check bool) "prefix core consists only of original assertions" true
    (Expr.Set.subset selected facts);
  let before = Expr.Set.elements facts in
  let types () = Hashtbl.fold (fun n t acc -> (n,t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_types = types () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "captured failed prefix restoration is impossible" true
      (Option.is_none (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) selected in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let content = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix content) in
    Alcotest.(check bool) "prefix core has real native proof" true (observed <> []);
    Printf.printf "LIST_PREFIX_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "prefix facts unchanged" true (before = Expr.Set.elements facts);
  Alcotest.(check bool) "prefix gamma unchanged" true (before_types = types ());
  Alcotest.(check bool) "without decomposition permits native counterexample" true
    (Option.is_some (Smt.exec_sat (Expr.Set.singleton failed) g));
  Alcotest.(check bool) "without failed goal permits native counterexample" true
    (Option.is_some (Smt.exec_sat (Expr.Set.singleton link) g))

let list_prefix_only_restore () =
  let facts = parse_gil_set [
    "(! (0. < #evidenceIndex))";
    "(! (0. < #index))";
    "(! (#evidenceIndex < #evidenceLen))";
    "(! (#index < #failingLen))";
    "(! (#key == none))";
    "(! (#lvar_480 < 1.))";
    "(! (#lvar_489 < 1.))";
    "(! (#previousErrors == empty))";
    "(! (#previousErrors == none))";
    "(! ((typeOf #previousErrors) == List))";
    "(! (l+ (#targetBefore, {{ #targetPrevious, #targetItem }}) == l-sub(l+ \n   (#targetBefore, {{ #targetPrevious, #targetItem }}, #targetTail), 0i, (3i i+ (-1i i* (l-len #targetTail))))))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_1348)";
    "(is_int #lvar_489)";
    "(is_int (4294967295. - (#lvar_1348 + 1.)))";
    "(is_int (#lvar_1348 + 1.))";
    "(is_int (#lvar_1348 - 1.))";
    "(0i i< (u16-len #confidence))";
    "(0i i<= (l-len #targetBefore))";
    "(0i i<= (l-len #targetTail))";
    "(0. == #failingLen)";
    "(0. < #lvar_1348)";
    "(0. <= #evidenceIndex)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #index)";
    "(0. <= #lvar_489)";
    "(0. <= (4294967295. - (#lvar_1348 + 1.)))";
    "(0. <= (#lvar_1348 + 1.))";
    "(0. <= (#lvar_1348 - 1.))";
    "(#evidenceIndex == 0.)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex == #evidenceLen)";
    "(#evidenceIndex <= #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == 0.)";
    "(#index == #failingLen)";
    "(#index == #index)";
    "(#index <= #failingLen)";
    "(#lvar_1024 v== {{ #lvar_1109,\n#lvar_1211 }})";
    "(#lvar_1110 v== {{ #lvar_1211 }})";
    "(#lvar_1324 v== (4294967295. - #index))";
    "(#lvar_1339 v== (4294967295. - #lvar_1348))";
    "(#lvar_1340 v== #targetItem)";
    "(#lvar_1341 v== #targetTail)";
    "(#lvar_1348 == #lvar_1348)";
    "(#lvar_1348 < 3.)";
    "(#lvar_142 v== #lvar_1010)";
    "(#lvar_142 v== #lvar_1327)";
    "(#lvar_142 v== #lvar_164)";
    "(#lvar_143 v== #lvar_1011)";
    "(#lvar_143 v== #lvar_1328)";
    "(#lvar_143 v== #lvar_165)";
    "(#lvar_145 v== #lvar_1013)";
    "(#lvar_145 v== #lvar_1330)";
    "(#lvar_145 v== #lvar_167)";
    "(#lvar_146 v== #lvar_1014)";
    "(#lvar_146 v== #lvar_1331)";
    "(#lvar_146 v== #lvar_168)";
    "(#lvar_164 v== #lvar_142)";
    "(#lvar_165 v== #lvar_143)";
    "(#lvar_167 v== #lvar_145)";
    "(#lvar_168 v== #lvar_146)";
    "(#lvar_489 == #lvar_489)";
    "(#lvar_489 <= (as_num (u16-len #confidence)))";
    "(#lvar_491 v== (4294967295. - #evidenceIndex))";
    "(#lvar_js_17 v== #lvar_142)";
    "(#lvar_js_17 v== #lvar_js_37)";
    "(#lvar_js_17 v== #lvar_js_41)";
    "(#lvar_js_17 v== #lvar_js_45)";
    "(#lvar_js_17 v== #lvar_js_53)";
    "(#lvar_js_18 v== #lvar_143)";
    "(#lvar_js_18 v== #lvar_js_38)";
    "(#lvar_js_18 v== #lvar_js_42)";
    "(#lvar_js_18 v== #lvar_js_46)";
    "(#lvar_js_18 v== #lvar_js_54)";
    "(#lvar_js_37 v== #lvar_js_17)";
    "(#lvar_js_38 v== #lvar_js_18)";
    "(#lvar_js_41 v== #lvar_js_17)";
    "(#lvar_js_42 v== #lvar_js_18)";
    "(#lvar_js_45 v== #lvar_js_17)";
    "(#lvar_js_46 v== #lvar_js_18)";
    "(#lvar_js_53 v== #lvar_js_17)";
    "(#lvar_js_54 v== #lvar_js_18)";
    "((u16-len #confidence) == 1i)";
    "((u16-len #confidence) i<= 9007199254740991i)";
    "((u16-len #lvar_1023) i<= 9007199254740991i)";
    "((u16-len #lvar_1109) i<= 9007199254740991i)";
    "((u16-len #lvar_1211) i<= 9007199254740991i)";
    "((u16-len #summary) i<= 9007199254740991i)";
    "((u16-len #targetItem) i<= 9007199254740991i)";
    "((u16-len #targetPrevious) i<= 9007199254740991i)";
    "((4294967295. - (#lvar_1348 + 1.)) < (4294967295. - #lvar_1348))";
    "((#lvar_1348 + 1.) <= 4294967295.)";
    "((#lvar_1348 - 1.) < 4294967295.)";
    "((#lvar_480 == 0.) or (#lvar_480 == 1.))";
    "(((#lvar_1348 + 1.) - 1.) == #lvar_1348)";
    "(((#lvar_1348 - 1.) + 1.) == #lvar_1348)";
    "(((#lvar_480 == 0.) and (#key == undefined)) or ((#lvar_480 == 1.) and \n(#key == u16\"classification\")))";
    "(((#lvar_489 == 0.) and ((u16-len #confidence) == 0i)) or ((1. <= #lvar_489) and (0. < (as_num (u16-len #confidence)))))";
    "({{ #lvar_1023, #lvar_1109,\n#lvar_1211 }} == l+ (#targetBefore, {{ #targetPrevious, #targetItem }},\n                     #targetTail))";
  ] |> Expr.Set.add
    (bin ValueEqual (Expr.LVar "#lvar_1212") (Expr.EList [])) in
  let gamma = Gamma.init () in
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#lvar_1339" Type.NumberType;
  Gamma.update gamma "#lvar_480" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_1109" Type.Utf16Type;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_1023" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_1324" Type.NumberType;
  Gamma.update gamma "#lvar_1348" Type.NumberType;
  Gamma.update gamma "#lvar_489" Type.NumberType;
  Gamma.update gamma "#lvar_1211" Type.Utf16Type;
  Gamma.update gamma "#targetItem" Type.Utf16Type;
  Gamma.update gamma "#targetBefore" Type.ListType;
  Gamma.update gamma "#targetTail" Type.ListType;
  Gamma.update gamma "#lvar_491" Type.NumberType;
  Gamma.update gamma "#targetPrevious" Type.Utf16Type;
  let g = Gamma.as_hashtbl gamma in
  let failed = Expr.Set.choose (parse_gil_set [ "(! (l+ (#targetBefore, {{ #targetPrevious, #targetItem }}) == l-sub(l+ \n   (#targetBefore, {{ #targetPrevious, #targetItem }}, #targetTail), 0i, (3i i+ (-1i i* (l-len #targetTail))))))" ]) in
  let link = Expr.Set.choose (parse_gil_set [ "({{ #lvar_1023, #lvar_1109,\n#lvar_1211 }} == l+ (#targetBefore, {{ #targetPrevious, #targetItem }},\n                     #targetTail))" ]) in
  let selected = Expr.Set.of_list [ failed; link ] in
  Alcotest.(check bool) "prefix core consists only of original assertions" true
    (Expr.Set.subset selected facts);
  let before = Expr.Set.elements facts in
  let types () = Hashtbl.fold (fun n t acc -> (n,t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_types = types () in
  let queries () = if Sys.file_exists "gillian_smt_queries" then
    Array.to_list (Sys.readdir "gillian_smt_queries") else [] in
  let before_queries = queries () and saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "captured failed prefix restoration is impossible" true
      (Option.is_none (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) selected in
    let observed = queries () |> List.filter (fun name ->
      if List.mem name before_queries then false else
      let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
      let content = Fun.protect ~finally:(fun () -> close_in ch)
        (fun () -> really_input_string ch (in_channel_length ch)) in
      String.starts_with ~prefix content) in
    Alcotest.(check bool) "prefix core has real native proof" true (observed <> []);
    Printf.printf "PREFIX_ONLY_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "prefix facts unchanged" true (before = Expr.Set.elements facts);
  Alcotest.(check bool) "prefix gamma unchanged" true (before_types = types ());
  Alcotest.(check bool) "without decomposition permits native counterexample" true
    (Option.is_some (Smt.exec_sat (Expr.Set.singleton failed) g));
  Alcotest.(check bool) "without failed goal permits native counterexample" true
    (Option.is_some (Smt.exec_sat (Expr.Set.singleton link) g))

let natural_counter_query () =
  (* Original caller feasibility query; capture SHA256: 76623267e07e1752b2373970bccb281ed770d27761170d70c392337537fb4b37. *)
  let facts = parse_gil_set [
    "(! (#evidenceIndex < #evidenceLen))";
    "(! (#index < #failingLen))";
    "(! (#lvar_473 < 1.))";
    "(! (#lvar_873 < 1.))";
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_873)";
    "(is_int #targetIndex)";
    "(is_int #targetLen)";
    "(is_int (#evidenceIndex - 1.))";
    "(is_int (#index - 1.))";
    "(0. < #evidenceIndex)";
    "(0. < #index)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_873)";
    "(0. <= #targetIndex)";
    "(0. <= #targetLen)";
    "(0. <= (#evidenceIndex - 1.))";
    "(0. <= (#index - 1.))";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex == #evidenceLen)";
    "(#evidenceIndex <= #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == #failingLen)";
    "(#index == #index)";
    "(#index <= #failingLen)";
    "(#lvar_1057 v== (4294967295. - #targetIndex))";
    "(#lvar_873 == #lvar_873)";
    "(#lvar_875 v== (4294967295. - #evidenceIndex))";
    "(#lvar_985 v== (4294967295. - #index))";
    "(#targetIndex == #targetIndex)";
    "(#targetIndex <= #targetLen)";
    "(#targetLen <= 4294967295.)";
    "((#evidenceIndex - 1.) < 4294967295.)";
    "((#index - 1.) < 4294967295.)";
    "((#lvar_473 == 0.) or (#lvar_473 == 1.))";
    "(((#evidenceIndex - 1.) + 1.) == #evidenceIndex)";
    "(((#index - 1.) + 1.) == #index)";
  ] in
  let gamma = Gamma.init () in
  Gamma.update gamma "#targetIndex" Type.NumberType;
  Gamma.update gamma "#before" Type.ListType;
  Gamma.update gamma "#previous" Type.Utf16Type;
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#lvar_1057" Type.NumberType;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#targetSuffix" Type.ListType;
  Gamma.update gamma "#lvar_873" Type.NumberType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_875" Type.NumberType;
  Gamma.update gamma "#evidenceBefore" Type.ListType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#lvar_473" Type.NumberType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#targetPrefix" Type.ListType;
  Gamma.update gamma "#lvar_985" Type.NumberType;
  let g = Gamma.as_hashtbl gamma in
  let before = Expr.Set.elements facts in
  let types () = Hashtbl.fold (fun n t acc -> (n,t) :: acc) g []
    |> List.sort Stdlib.compare in
  let before_types = types () in
  let saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    let counters = ["#evidenceLen"; "#failingLen"; "#targetLen"] in
    let seeded = List.fold_left (fun acc name -> Expr.Set.add
      (bin ValueEqual (Expr.LVar name) (Expr.num 1.)) acc) facts counters in
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) seeded in
    Alcotest.(check bool) "original bounded-counter query has native full SAT witness" true
      (Option.is_some (Smt.check_sat facts g));
    let observed = Array.to_list (Sys.readdir "gillian_smt_queries")
      |> List.filter (fun name ->
        let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
        let content = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        String.starts_with ~prefix content) in
    Alcotest.(check bool) "native hint retains every original assertion" true
      (observed <> []);
    Printf.printf "NATURAL_COUNTER_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "counter hint does not mutate facts" true
    (before = Expr.Set.elements facts);
  Alcotest.(check bool) "counter hint does not mutate gamma" true
    (before_types = types ());
  Hashtbl.add g "#counter_list" Type.ListType;
  let len = Expr.UnOp (LstLen, Expr.LVar "#counter_list") in
  let conflict = Expr.Set.add (bin Equal len (Expr.int 1))
    (Expr.Set.add (bin Equal len (Expr.int 2)) facts) in
  Alcotest.(check bool) "non-numeric contradiction cannot become a counter witness" true
    (Option.is_none (Smt.check_sat conflict g));
  let zero = Expr.Set.add (bin ValueEqual (Expr.LVar "#targetLen") (Expr.num 0.)) facts in
  Alcotest.(check bool) "original zero binding survives the candidate hint" true
    (Option.is_some (Smt.check_sat zero g));
  let rounding = Expr.LVar "#rounding_counter" in
  Hashtbl.add g "#rounding_counter" Type.NumberType;
  let rounded = Expr.Set.of_list [Expr.UnOp (IsInt, rounding);
    bin FLessThanEqual (Expr.num 0.) rounding;
    bin ValueEqual rounding (Expr.num 9007199254740992.);
    not_ (bin ValueEqual (bin FPlus rounding (Expr.num 1.)) rounding)] in
  Alcotest.(check bool) "binary64 rounded increment remains impossible" true
    (Option.is_none (Smt.check_sat (Expr.Set.union facts rounded) g))

let literal_counter_contradiction () =
  (* Original caller query SHA256: 7c71c39111f11a4db5d198c537a90dbeab3ee116eb4c539ef93daef47e0b6a90. *)
  let facts = parse_gil_set [
    "(is_int #evidenceIndex)";
    "(is_int #evidenceLen)";
    "(is_int #failingLen)";
    "(is_int #index)";
    "(is_int #lvar_873)";
    "(is_int #targetLen)";
    "(0. < #evidenceIndex)";
    "(0. < #index)";
    "(0. <= #evidenceLen)";
    "(0. <= #failingLen)";
    "(0. <= #lvar_873)";
    "(0. <= #targetLen)";
    "(#evidenceIndex == #evidenceIndex)";
    "(#evidenceIndex == #evidenceLen)";
    "(#evidenceIndex <= #evidenceLen)";
    "(#evidenceLen == #evidenceLen)";
    "(#evidenceLen <= 4294967295.)";
    "(#failingLen == #failingLen)";
    "(#failingLen <= 4294967295.)";
    "(#index == 0.)";
    "(#index == #index)";
    "(#index < #failingLen)";
    "(#lvar_873 == #lvar_873)";
    "(#targetLen <= 4294967295.)";
  ] in
  let gamma = Gamma.init () in
  Gamma.update gamma "#summary" Type.Utf16Type;
  Gamma.update gamma "#evidenceIndex" Type.NumberType;
  Gamma.update gamma "#prototype" Type.ObjectType;
  Gamma.update gamma "#lvar_873" Type.NumberType;
  Gamma.update gamma "#suffix" Type.ListType;
  Gamma.update gamma "#targetValues" Type.ListType;
  Gamma.update gamma "#failingLen" Type.NumberType;
  Gamma.update gamma "#index" Type.NumberType;
  Gamma.update gamma "#evidenceLen" Type.NumberType;
  Gamma.update gamma "#lvar_1171" Type.NumberType;
  Gamma.update gamma "#lvar_875" Type.NumberType;
  Gamma.update gamma "#evidenceBefore" Type.ListType;
  Gamma.update gamma "#lvar_148" Type.ObjectType;
  Gamma.update gamma "#targetLen" Type.NumberType;
  Gamma.update gamma "#retryable" Type.BooleanType;
  Gamma.update gamma "#lvar_473" Type.NumberType;
  Gamma.update gamma "#confidence" Type.Utf16Type;
  Gamma.update gamma "#lvar_147" Type.ObjectType;
  let g = Gamma.as_hashtbl gamma in
  let comparison = Expr.Set.choose (parse_gil_set ["(0. < #index)"]) in
  let binding = Expr.Set.choose (parse_gil_set ["(#index == 0.)"]) in
  let core = Expr.Set.of_list [ comparison; binding ] in
  let original_facts = Expr.Set.elements facts in
  let original_gamma = Hashtbl.fold (fun n t acc -> (n,t)::acc) g []
    |> List.sort Stdlib.compare in
  let saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    Alcotest.(check bool) "complete original literal contradiction is UNSAT" true
      (Option.is_none (Smt.check_sat facts g));
    let prefix = Fmt.str "GIL query:\nFS: %a\nGAMMA: "
      (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) core in
    let observed = Array.to_list (Sys.readdir "gillian_smt_queries")
      |> List.filter (fun name ->
        let ch = open_in_bin (Filename.concat "gillian_smt_queries" name) in
        let content = Fun.protect ~finally:(fun () -> close_in ch)
          (fun () -> really_input_string ch (in_channel_length ch)) in
        String.starts_with ~prefix content) in
    Alcotest.(check bool) "native contradiction query is exactly two original atoms" true
      (observed <> []);
    Printf.printf "LITERAL_COUNTER_NATIVE_QUERY=%s\n%!" (List.hd observed));
  Alcotest.(check bool) "literal core does not mutate original facts" true
    (original_facts = Expr.Set.elements facts);
  Alcotest.(check bool) "literal core does not mutate original gamma" true
    (original_gamma = (Hashtbl.fold (fun n t acc -> (n,t)::acc) g []
      |> List.sort Stdlib.compare));
  Alcotest.(check bool) "removing original literal binding permits native SAT" true
    (Option.is_some (Smt.check_sat (Expr.Set.singleton comparison) g));
  Alcotest.(check bool) "removing original comparison permits native SAT" true
    (Option.is_some (Smt.check_sat (Expr.Set.singleton binding) g));
  let possible = parse_gil_set ["(#index v== 1.)"; "(0. < #index)"] in
  Alcotest.(check bool) "consistent literal comparison remains native SAT" true
    (Option.is_some (Smt.check_sat possible g));
  let signed_zero = parse_gil_set ["(#index == -0.)"; "(0. < #index)"] in
  Alcotest.(check bool) "signed zero cannot satisfy positive comparison" true
    (Option.is_none (Smt.check_sat signed_zero g))


let integer_order_count_core () =
  let names = Expr.LVar "#core_names" and values = Expr.LVar "#core_values" in
  let n = Expr.LVar "#core_length" in
  let len = Expr.UnOp (LstLen, names) and count = Expr.UnOp (NumToInt, n) in
  let g = Gamma.init () in
  List.iter (fun name -> Gamma.update g name Type.ListType)
    ["#core_names"; "#core_values"];
  Gamma.update g "#core_length" Type.NumberType;
  let gt = Gamma.as_hashtbl g in
  let is_int = Expr.UnOp (IsInt,n) in
  let link = bin Equal len count in
  let bound = bin ILessThanEqual count (Expr.int 4294967294) in
  let position = bin KeyInsertIndex
    (Expr.NOp (LstCat,[names; Expr.EList [Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "length"))]]))
    (Expr.UnOp (NumberToUtf16,n)) in
  let placement = bin Equal position len in
  let facts = Expr.Set.of_list [
    is_int; link; bound; placement;
    Expr.UnOp (LstAllUtf16,names);
    bin ILessThanEqual (Expr.int 0) len;
    bin ILessThanEqual (Expr.int 0) count;
    bin Equal len (Expr.UnOp (LstLen,values));
    bin FLessThanEqual (Expr.num 0.) n;
    bin FLessThan n (Expr.num 4294967295.);
    not_ (bin ValueEqual n (Expr.num (-0.)));
    not_ (bin LstContains names (Expr.Lit (Utf16String (Gillian.Utils.Utf16.of_canonical "length"))));
    not_ (bin LstContains names (Expr.UnOp (NumberToUtf16,n)));
  ] in
  let saved_dump = !Config.dump_smt in
  Config.dump_smt := true;
  Fun.protect ~finally:(fun () -> Config.dump_smt := saved_dump) (fun () ->
    let core fs failed =
      let fs = Expr.Set.add failed fs in
      match Solver.integer_order_core fs gt failed with
      | None -> failwith "expected original integer core"
      | Some selected ->
          Alcotest.(check bool) "integer core contains only original assertions" true
            (Expr.Set.mem failed selected && Expr.Set.subset selected fs);
          selected
    in
    List.iter (fun limit ->
      let failed = bin ILessThanEqual (Expr.Lit (Int limit)) len in
      let selected = core facts failed in
      Alcotest.(check bool) "count core keeps both alias and bound" true
        (Expr.Set.mem link selected && Expr.Set.mem bound selected);
      Alcotest.(check bool) "host bound core omits unrelated scan machinery" false
        (Expr.Set.mem placement selected);
      Alcotest.(check bool) "original full-range list bound has native UNSAT core" true
        (Smt.proves_unsat selected gt);
      Alcotest.(check bool) "full entailment uses the checked bound" true
        (Solver.check_entailment Utils.Containers.SS.empty
           (Engine.PFS.of_list (Expr.Set.elements facts)) [not_ failed] g)
    ) [Z.of_int 4294967295; Z.of_int max_int; Z.pred (Z.of_int max_int)];
    List.iter (fun failed ->
      let selected = core facts failed in
      Alcotest.(check bool) "position core retains actual placement equality" true
        (Expr.Set.mem placement selected);
      Alcotest.(check bool) "actual insertion position guard has native UNSAT core" true
        (Smt.proves_unsat selected gt)
    ) [bin ILessThan position (Expr.int 0);
       bin ILessThanEqual (bin IPlus len (Expr.int 2)) position];
    (* Small bounds give actual SAT models, without asking the solver to
       materialize a host-sized concrete list for a negative control. *)
    let small_bound = bin ILessThanEqual count (Expr.int 3) in
    let failed = bin ILessThanEqual (Expr.int 4) len in
    let small = facts |> Expr.Set.remove bound |> Expr.Set.remove placement
      |> Expr.Set.add small_bound in
    List.iter (fun omitted ->
      let selected = core (Expr.Set.remove omitted small) failed in
      Alcotest.(check bool) "omitting count alias or bound permits native SAT" true
        (Option.is_some (Smt.check_sat selected gt))
    ) [link; small_bound];
    let full = Expr.Set.add failed small in
    List.iter (fun name ->
      let missing = Hashtbl.copy gt in
      Hashtbl.remove missing name;
      let selected = Solver.integer_order_core full missing failed in
      Alcotest.(check bool) "missing original count/list type cannot prove UNSAT" false
        (match selected with Some selected -> Smt.proves_unsat selected missing | None -> false)
    ) ["#core_names"; "#core_length"];
    let selected = core (Expr.Set.remove is_int small) failed in
    Alcotest.(check bool) "omitting integrality leaves a native countermodel" true
      (Option.is_some (Smt.check_sat selected gt));
    let partial = Expr.UnOp (LstLen,Expr.LstSub(names,Expr.int (-1),Expr.int 1)) in
    let unsafe = bin ILessThanEqual partial (Expr.int 3) in
    Alcotest.(check bool) "a partial length cannot authorize a core" true
      (Option.is_none (Solver.integer_order_core (Expr.Set.singleton unsafe) gt unsafe));
    let flag = Expr.LVar "#core_flag" in
    Gamma.update g "#core_flag" Type.BooleanType;
    let premises = [bin ILessThanEqual count (Expr.int 3); is_int; flag;
      not_ (bin Equal count (Expr.int 2))] in
    let goal = bin Or (bin ILessThan count (Expr.int 0)) flag in
    Alcotest.(check bool) "inconclusive integer subset retains complete fallback" true
      (Solver.check_entailment Utils.Containers.SS.empty
        (Engine.PFS.of_list premises) [goal] g);
    Printf.printf "INTEGER_ORDER_COUNT_CORE_NATIVE_CONTROLS_COMPLETE\n%!"
  )

let uint32_alias_complete_query () =
  (* Original AP_push query171 premises: formatter links and signed-zero-safe
     conversion facts must stay with the complete counterquery. *)
  let g = Gamma.init () in
  List.iter (fun n -> Gamma.update g n Type.NumberType)
    ["#uint32_count"; "#uint32_length"];
  Gamma.update g "#uint32_values" Type.ListType;
  let facts = parse_gil_set [
    "(is_int #uint32_count)";
    "(0. <= #uint32_count)";
    "(#uint32_count < 4294967295.)";
    "(#uint32_length == #uint32_count)";
    "((num_to_int #uint32_count) v== #uint32_count)";
    "((num_to_uint32 #uint32_count) v== (#uint32_count + 0.))";
    "((num_to_uint32 (#uint32_count + 0.)) v== (#uint32_count + 0.))";
    "((num_to_uint32 (#uint32_count + 1.)) v== (#uint32_count + 1.))";
    "(((num_to_uint32 (#uint32_count + 0.)) + 1.) v== (#uint32_count + 1.))";
    "((num_to_utf16 (num_to_uint32 (#uint32_count + 0.))) == (num_to_utf16 #uint32_count))";
    "((num_to_utf16 (num_to_uint32 (#uint32_length + 0.))) == (num_to_utf16 #uint32_length))";
    "(0i i<= (l-len #uint32_values))";
  ] in
  let goal = bin FLessThan
    (Expr.UnOp (ToUint32Op, bin FPlus (Expr.LVar "#uint32_length") (Expr.num 0.)))
    (Expr.UnOp (ToUint32Op, Expr.LVar "#uint32_count")) in
  let check name expected facts goal =
    Alcotest.(check bool) name expected
      (Solver.check_entailment Utils.Containers.SS.empty
        (Engine.PFS.of_list (Expr.Set.elements facts)) [goal] g) in
  let before = Expr.Set.elements facts in
  check "Uint32 same-length false goal retains a complete SAT witness" false facts goal;
  check "Uint32 same-length ordering remains proved" true facts (not_ goal);
  let zero = bin ValueEqual (Expr.LVar "#uint32_count") (Expr.num (-0.)) in
  check "Uint32 signed-zero alias ordering remains proved" true
    (Expr.Set.add zero facts) (not_ goal);
  let alias = bin Equal (Expr.LVar "#uint32_length") (Expr.LVar "#uint32_count") in
  let no_alias = Expr.Set.remove alias facts in
  check "missing length alias cannot prove the ordering" false no_alias (not_ goal);
  Alcotest.(check bool) "Uint32 eligibility leaves original facts unchanged" true
    (before = Expr.Set.elements facts);
  Printf.printf "UINT32_COMPLETE_QUERY_CONTROLS_FINISHED\n%!"

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
    Alcotest.test_case "original UTF16 code-order core and counterexamples"
      `Quick (with_total utf16_code_order_core);
    Alcotest.test_case "original finite_add shared core" `Quick
      (with_total original_finite_add_core);
    Alcotest.test_case "original code_upper shared core" `Quick
      (with_total original_code_upper_core);
    Alcotest.test_case "original length_index shared core" `Quick
      (with_total original_length_index_core);
    Alcotest.test_case "complete numeric dependencies avoid focused loss" `Quick
      (with_total numeric_dependency_focus);
    Alcotest.test_case "original mask_lower core" `Quick
      (with_total original_mask_lower_core);
    Alcotest.test_case "original mask_upper core" `Quick
      (with_total original_mask_upper_core);
    Alcotest.test_case "original mask_complement core" `Quick
      (with_total original_mask_complement_core);
    Alcotest.test_case "original numeric length projection and collisions" `Quick
      (with_total original_length_projection);
    Alcotest.test_case "UTF16 integer lengths retain numeric aliases" `Quick
      (with_total utf16_length_alias_contained);
    Alcotest.test_case "UTF16 focused lengths retain numeric dependencies" `Quick
      (with_total utf16_length_focused_dependencies);
    Alcotest.test_case "simplified rank goal retains numeric pieces" `Quick
      (with_total simplified_rank_goal);
    Alcotest.test_case "positive array counter keeps complete SAT query" `Quick
      (with_total (array_counter_witness false));
    Alcotest.test_case "zero array counter keeps complete SAT query" `Quick
      (with_total (array_counter_witness true));
    Alcotest.test_case "array predecessor keeps complete SAT query" `Quick
      (with_total array_predecessor_witness);
    Alcotest.test_case "independent array counters retain complete SAT query" `Quick
      (with_total independent_array_counters);
    Alcotest.test_case "carried counter roots retain complete SAT query" `Quick
      (with_total carried_counter_witness);
    Alcotest.test_case "singleton surrogate retains complete SAT query" `Quick
      (with_total singleton_surrogate_witness);
    Alcotest.test_case "fixed pair retains complete SAT query" `Quick
      (with_total fixed_pair_witness);
    Alcotest.test_case "paired surrogate retains complete SAT query" `Quick
      (with_total paired_surrogate_witness);
    Alcotest.test_case "ordinary singleton retains complete SAT query" `Quick
      (with_total ordinary_singleton_witness);
    Alcotest.test_case "carried bounds retain complete SAT query" `Quick
      (with_total carried_bounds_witness);
    Alcotest.test_case "literal-bound chain retains complete SAT query" `Quick
      (with_total fixed_chain_witness);
    Alcotest.test_case "bounded root preserves complete list query" `Quick
      (with_total bounded_counter_witness);
    Alcotest.test_case "rank disjunction uses original numeric cases" `Quick
      (with_total rank_case_split);
    Alcotest.test_case "original list-prefix restoration core" `Quick
      (with_total list_prefix_restore);
    Alcotest.test_case "original inverse list-prefix restoration core" `Quick
      (with_total list_prefix_only_restore);
    Alcotest.test_case "bounded natural counters retain complete SAT query" `Quick
      (with_total natural_counter_query);
    Alcotest.test_case "original literal counter contradiction core" `Quick
      (with_total literal_counter_contradiction);
    Alcotest.test_case "integer count bounds retain original aliases" `Quick
      (with_total integer_order_count_core);
    Alcotest.test_case "Uint32 aliases retain complete counterqueries" `Quick
      (with_total uint32_alias_complete_query);
  ]
