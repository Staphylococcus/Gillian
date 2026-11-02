(* Focused tests for the GIL-only slice bridge. No non-TOTAL agreement claim. *)
open Gillian.Gil_syntax
module Codec = Gillian.Utils.Utf16
module Gamma = Gillian.Symbolic.Type_env
module Reduction = Gillian.Logic.Reduction
module Typing = Engine.Typing
module State = Gillian.Symbolic.SState.Make (Semantics.Symbolic)
module Totality = Engine.Totality
module Config = Gillian.Utils.Config
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let bin op a b = Expr.BinOp (a, op, b)
let value units =
  Expr.Lit (Literal.Utf16String (Codec.of_canonical (Codec.of_code_units units)))
let slice s start count = Expr.NOp (Utf16Sub, [ s; start; count ])
let length s = Expr.UnOp (Utf16Len, s)
let check label ok = Alcotest.(check bool) label true ok
let store () = Engine.CExprEval.CStore.init []
let with_total f () =
  let old = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := old) f

let concrete_and_reduction () =
  List.iter
    (fun (units, start, count, expected) ->
      let term = slice (value units) (Expr.int start) (Expr.int count) in
      let expected = value expected in
      check "actual concrete evaluator preserves exact UTF16 units"
        (Expr.equal expected (Expr.Lit (Engine.CExprEval.evaluate_expr (store ()) term)));
      check "actual ground reducer agrees with independent sublist expectation"
        (Expr.equal expected (Reduction.reduce_lexpr term)))
    [ ([], 0, 0, []); ([65], 1, 0, []);
      ([65; 0xd83d; 0xde00; 66], 1, 1, [0xd83d]);
      ([65; 0xd83d; 0xde00; 66], 2, 1, [0xde00]);
      ([0; 0xd800; 0xdfff; 0xffff], 0, 4, [0; 0xd800; 0xdfff; 0xffff]);
      ([0xd800; 65; 0xdfff], 1, 1, [65]) ]

let invalid_operands () =
  let huge = Expr.Lit (Literal.Int (Z.pow (Z.of_int 10) 1000)) in
  let s = value [65] in
  let terms =
    [ slice s (Expr.int (-1)) (Expr.int 0);
      slice s (Expr.int 0) (Expr.int (-1));
      slice s (Expr.int 1) (Expr.int 1);
      slice s (Expr.int 2) (Expr.int 0);
      slice s huge (Expr.int 0); slice s (Expr.int 0) huge;
      slice (Expr.string "bytes") (Expr.int 0) (Expr.int 0);
      slice (Expr.num 0.) (Expr.int 0) (Expr.int 0);
      slice s (Expr.num 0.) (Expr.int 1);
      slice s (Expr.int 0) (Expr.num 1.);
      Expr.NOp (Utf16Sub, []);
      Expr.NOp (Utf16Sub, [s; Expr.int 0]);
      Expr.NOp (Utf16Sub, [s; Expr.int 0; Expr.int 0; Expr.int 0]) ]
  in
  List.iter
    (fun term ->
      check "concrete invalid slice rejects before any unsafe host cast"
        (try ignore (Engine.CExprEval.evaluate_expr (store ()) term); false with
         | Engine.CExprEval.TypeError _ | Engine.CExprEval.EvaluationError _ -> true);
      check "ground reduction propagates invalid slice"
        (try ignore (Reduction.reduce_lexpr term); false with
         | Reduction.ReductionException _ -> true))
    terms

let actual_typing_paths () =
  let s = Expr.LVar "#slice_s" and a = Expr.LVar "#slice_start"
  and n = Expr.LVar "#slice_count" in
  let term = slice s a n in
  let gamma = Gamma.init () in
  Typing.infer_types_expr gamma term;
  List.iter
    (fun (name, typ) ->
      check "operand inference records exact Utf16/Int types"
        (Option.equal Type.equal (Gamma.get gamma name) (Some typ)))
    ["#slice_s", Type.Utf16Type; "#slice_start", Type.IntType;
     "#slice_count", Type.IntType];
  check "type_lexpr returns Utf16" (Typing.type_lexpr gamma term = (Some Type.Utf16Type, true));
  check "symbolic reducer retains exact slice term"
    (Expr.equal term (Reduction.reduce_lexpr ~gamma term));
  let inferred = Option.get (Typing.reverse_type_lexpr true (Gamma.init ()) [term, Type.Utf16Type]) in
  check "reverse result inference reaches Int start"
    (Option.equal Type.equal (Gamma.get inferred "#slice_start") (Some Type.IntType));
  check "wrong result type cannot infer a slice"
    (Typing.reverse_type_lexpr true (Gamma.init ()) [term, Type.ListType] = None);
  List.iter
    (fun bad -> check "typing rejects wrong kinds and malformed arity"
      (snd (Typing.type_lexpr (Gamma.init ()) bad) = false))
    [slice (Expr.string "bytes") (Expr.int 0) (Expr.int 0);
     slice (value []) (Expr.num 0.) (Expr.int 0);
     slice (value []) (Expr.int 0) (Expr.num 0.);
     Expr.NOp (Utf16Sub, []); Expr.NOp (Utf16Sub, [value []; Expr.int 0])]

let expression_syntax () =
  List.iter
    (fun term ->
      let printed = Fmt.str "%a" Expr.pp term in
      check "actual GIL parser roundtrips the slice operator"
        (match Parser.parse_expression (Lexing.from_string printed) with
         | Ok recovered -> Expr.equal term recovered | Error _ -> false))
    [slice (value []) (Expr.int 0) (Expr.int 0);
     slice (value [0xd800; 0xdfff]) (Expr.int 1) (Expr.int 1);
     slice (Expr.LVar "#s") (Expr.int 0) (length (Expr.LVar "#s"))];
  check "literal mathematical Int syntax is accepted"
    (match Parser.parse_expression (Lexing.from_string "u16-sub(u16\"A\", 0i, 1i)") with
     | Ok recovered -> Expr.equal recovered (slice (value [65]) (Expr.int 0) (Expr.int 1))
     | Error _ -> false)

let proof_check state term =
  Totality.check_proof_expression ~context:"UTF16 slice unit"
    ~evaluate:(State.eval_expr state)
    ~assertion:(fun fact -> State.assert_a state [fact]) term

let domain_failure f =
  check "real incoming-state TOTAL definedness rejection"
    (try f (); false with
     | Gillian.Utils.Gillian_result.Exc.Gillian_error (AnalysisFailures [failure]) ->
         String.starts_with ~prefix:"UTF16 slice unit is not proved defined:" failure.msg)

let incoming_state_domains () =
  let s = Expr.LVar "#slice_input" in
  let state = Option.get (State.assume_t (State.init ()) s Type.Utf16Type) in
  (* No contents or length bound is assumed for the arbitrary input. *)
  proof_check state (slice s (Expr.int 0) (length s));
  proof_check state (slice s (length s) (Expr.int 0));
  let missing_bound = slice s (Expr.int 1) (Expr.int 0) in
  (* Equality can erase its value; its original partial operand must still be checked. *)
  domain_failure (fun () -> proof_check state (bin Equal missing_bound missing_bound));
  let nonempty = Option.get (State.assume_a (State.copy state)
      [bin ILessThanEqual (Expr.int 1) (length s)]) in
  proof_check nonempty (bin Equal missing_bound missing_bound);
  List.iter
    (fun term -> domain_failure (fun () -> proof_check state (bin Equal term term)))
    [slice s (Expr.int (-1)) (Expr.int 0);
     slice s (Expr.int 0) (Expr.int (-1));
     slice (value []) (Expr.int 0) (Expr.int 1);
     slice s (Expr.num 0.) (Expr.int 0);
     slice (Expr.LVar "#untyped") (Expr.int 0) (Expr.int 0)];
  let a = Expr.LVar "#slice_a" and n = Expr.LVar "#slice_n" in
  let typed = Option.get (State.assume_t (State.copy state) a Type.IntType) in
  let typed = Option.get (State.assume_t typed n Type.IntType) in
  domain_failure (fun () -> proof_check typed (slice s a n));
  let bounds = [bin ILessThanEqual (Expr.int 0) a; bin ILessThanEqual (Expr.int 0) n;
                bin ILessThanEqual (bin IPlus a n) (length s)] in
  let valid = Option.get (State.assume_a (State.copy typed) bounds) in
  proof_check valid (slice s a n);
  (* Each required mathematical inequality is independently load-bearing. *)
  List.iteri
    (fun omitted _ ->
      let remaining = List.filteri (fun index _ -> index <> omitted) bounds in
      let incomplete = Option.get (State.assume_a (State.copy typed) remaining) in
      domain_failure (fun () -> proof_check incomplete (slice s a n)))
    bounds

let executable_and_arity_guards () =
  let term = slice (value []) (Expr.int 0) (Expr.int 0) in
  let unsupported f =
    check "exact proof-only/arity guard rejects"
      (try f (); false with
       | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError msg) ->
           String.ends_with ~suffix:"UTF-16 slicing is a three-argument proof expression only." msg)
  in
  unsupported (fun () -> Totality.check_expression
    ~require:(fun _ _ -> Alcotest.fail "executable slice reached a domain requirement")
    ~proves:(fun _ -> false) ~evaluate:Fun.id term);
  List.iter (fun term -> unsupported (fun () -> proof_check (State.init ()) term))
    [Expr.NOp (Utf16Sub, []); Expr.NOp (Utf16Sub, [value []; Expr.int 0]);
     Expr.NOp (Utf16Sub, [value []; Expr.int 0; Expr.int 0; Expr.int 0])]

let complete_lemma_syntax () =
  let file = Option.value (Sys.getenv_opt "S05_TRIM_LEMMA_SOURCE")
      ~default:"Gillian-JS/Examples/S05TrimNonexpansion.gil" in
  match Parser.parse_eprog_from_file file with
  | Error _ -> Alcotest.fail "actual full recursive lemma did not parse"
  | Ok parsed ->
      let lemma = Prog.get_lemma_exn parsed.labeled_prog "S05TrimNonexpansion" in
      check "one actual lemma and no procedures" (Hashtbl.length parsed.labeled_prog.lemmas = 1
        && Hashtbl.length parsed.labeled_prog.procs = 0);
      check "actual formal and exact mathematical rank" (lemma.lemma_params = ["s"]
        && Option.equal Expr.equal lemma.lemma_variant (Some (length (Expr.LVar "#s"))));
      let spec = List.hd lemma.lemma_specs in
      check "actual precondition remains unrestricted Utf16 type"
        (fst spec.lemma_hyp = [Asrt.Types [Expr.LVar "#s", Type.Utf16Type]]);
      let calls = ref 0 and slices = ref 0 in
      let rec visit = function
        | LCmd.If (_, yes, no) -> List.iter visit yes; List.iter visit no
        | LCmd.SL (ApplyLem ("S05TrimNonexpansion", [_], [])) -> incr calls
        | LCmd.SL (SepAssert (_, [_])) -> incr slices
        | _ -> ()
      in
      let proof = Option.get lemma.lemma_proof in
      List.iter visit proof;
      Alcotest.(check int) "two actual recursive calls" 2 !calls;
      Alcotest.(check int) "four actual slice witness commands" 4 !slices


(* The original seven slice tests above stay unchanged. These tests call the
   public reducer with real PFS/gamma and use the concrete evaluator as oracle. *)
module PFS = Gillian.Symbolic.Pure_context

let trim s = Expr.UnOp (Utf16Trim, s)
let edge_s = Expr.LVar "#edge_s"
let edge_n = length edge_s
let edge_k = bin IPlus (Expr.int (-1)) edge_n
let edge_h = slice edge_s (Expr.int 0) (Expr.int 1)
let edge_t = slice edge_s edge_k (Expr.int 1)
let edge_p = slice edge_s (Expr.int 0) edge_k
let edge_ph = slice edge_p (Expr.int 0) (Expr.int 1)
let edge_eq a b = bin Equal a b
let edge_no a b = Expr.UnOp (Not, edge_eq a b)
let edge_space = Codec.whitespace_code_units
let edge_nonwhite = List.map (fun u -> edge_no edge_h (value [u])) edge_space
let edge_white = Expr.disjunct (List.map (fun u -> edge_eq edge_t (value [u])) edge_space)
let edge_facts =
  [bin ILessThan (Expr.int 1) edge_n;
   bin ILessThan (Expr.int 0) (length edge_p);
   edge_eq edge_ph edge_h; edge_white] @ edge_nonwhite

let edge_gamma () =
  let g = Gamma.init () in
  Gamma.update g "#edge_s" Type.Utf16Type; g

let gamma_pairs g =
  Gamma.get_var_type_pairs g |> List.of_seq |> List.sort Stdlib.compare

let edge_reduce ?(total=true) gamma facts =
  let old_total = !Config.Verification.total in
  Config.Verification.total := total;
  Fun.protect ~finally:(fun () -> Config.Verification.total := old_total)
    (fun () ->
      let pfs = PFS.of_list facts in
      let before_pfs = PFS.copy pfs and before_gamma = gamma_pairs gamma in
      Fun.protect ~finally:(fun () ->
        check "edge reduction preserves exact PFS" (PFS.equal before_pfs pfs);
        check "edge reduction preserves gamma" (before_gamma = gamma_pairs gamma))
        (fun () -> Reduction.reduce_lexpr ~pfs ~gamma (trim edge_s)))

let expect_edge label facts =
  check label (Expr.equal (trim edge_p) (edge_reduce (edge_gamma ()) facts))

let expect_opaque label facts =
  check label (Expr.equal (trim edge_s) (edge_reduce (edge_gamma ()) facts))

let edge_table_exhaustive () =
  Alcotest.(check int) "shared table has25 unique units" 25
    (List.length (List.sort_uniq Int.compare edge_space));
  for unit = 0 to 0xffff do
    let text = Codec.of_canonical (Codec.of_code_units [unit]) in
    let concrete_empty = Codec.trim (Codec.to_canonical text) = "" in
    if concrete_empty <> List.mem unit edge_space then
      Alcotest.failf "shared table disagrees with original concrete trim at U+%04X" unit
  done

let edge_exact_positive_facts () =
  expect_edge "canonical trailing step" edge_facts;
  expect_edge "positive conjunction facts"
    [List.fold_left (bin And) Expr.true_ edge_facts];
  expect_edge "integer bound alternate"
    (bin ILessThanEqual (Expr.int 2) edge_n :: List.tl edge_facts);
  let reverse = List.map (function
    | Expr.BinOp (a, Equal, b) -> edge_eq b a
    | UnOp (Not, BinOp (a, Equal, b)) -> edge_no b a
    | e -> e) edge_facts in
  expect_edge "equality orientations" reverse;
  List.iter (fun count ->
    let from = edge_k in
    let replace = Expr.subst_expr_for_expr ~to_subst:from ~subst_with:count in
    expect_edge "equivalent exact minus-one syntax" (List.map replace edge_facts))
    [bin IMinus edge_n (Expr.int 1); bin IPlus edge_n (Expr.int (-1))]

let edge_every_missing_guard () =
  List.iteri (fun omitted _ ->
    expect_opaque (Printf.sprintf "required fact%d independently loadbearing" omitted)
      (List.filteri (fun i _ -> i <> omitted) edge_facts)) edge_facts

let edge_one_hop_aliases () =
  let g = edge_gamma () in
  let h = Expr.LVar "#edge_head" and t = Expr.LVar "#edge_last"
  and p = Expr.LVar "#edge_prefix" and n = Expr.LVar "#edge_length"
  and k = Expr.LVar "#edge_count" in
  List.iter (fun name -> Gamma.update g name Type.Utf16Type)
    ["#edge_head";"#edge_last";"#edge_prefix"];
  List.iter (fun name -> Gamma.update g name Type.IntType)
    ["#edge_length";"#edge_count"];
  let facts =
    [edge_eq h edge_h; edge_eq t edge_t; edge_eq p edge_p;
     edge_eq n edge_n; edge_eq k edge_k;
     bin ILessThan (Expr.int 1) n;
     bin ILessThan (Expr.int 0) (length p);
     edge_eq (slice p (Expr.int 0) (Expr.int 1)) h;
     Expr.disjunct (List.map (fun u -> edge_eq t (value [u])) edge_space)]
    @ List.map (fun u -> edge_no h (value [u])) edge_space in
  check "typed one-hop aliases" (Expr.equal (trim edge_p) (edge_reduce g facts));
  let remove_binding = List.filter (fun e -> not (Expr.equal e (edge_eq h edge_h))) facts in
  check "missing alias definition stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g remove_binding));
  let cyclic = edge_eq h (slice h (Expr.int 0) (Expr.int 1)) :: remove_binding in
  check "self-referential slice alias stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g cyclic));
  let h2 = Expr.LVar "#edge_head2" in
  Gamma.update g "#edge_head2" Type.Utf16Type;
  let chain = edge_eq h h2 :: edge_eq h2 edge_h :: remove_binding in
  check "two-hop alias chain stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g chain));
  let two_cycle = edge_eq h h2 :: edge_eq h2 h :: remove_binding in
  check "two-variable cycle stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g two_cycle));
  let trim_alias = edge_eq h (trim edge_s) :: remove_binding in
  check "trim-bearing alias is no premise"
    (Expr.equal (trim edge_s) (edge_reduce g trim_alias));
  Gamma.remove g "#edge_head";
  Gamma.update g "#edge_head" Type.StringType;
  check "wrong original alias type stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g facts));
  Gamma.remove g "#edge_head";
  check "unknown original alias type stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce g facts))

let edge_reject_unrelated_facts () =
  let without_white = List.filter (fun e -> not (Expr.equal e edge_white)) edge_facts in
  expect_opaque "nonwhite OR leaf blocks shortcut"
    (bin Or edge_white (edge_eq edge_t (value [65])) :: without_white);
  expect_opaque "unknown OR leaf blocks shortcut"
    (bin Or edge_white (Expr.LVar "#edge_unknown") :: without_white);
  expect_opaque "white fact under implication is no premise"
    (bin Impl Expr.true_ edge_white :: without_white);
  expect_opaque "white fact under negation is no premise"
    (Expr.UnOp (Not, edge_white) :: without_white);
  expect_opaque "desired trim equality alone is no premise"
    [edge_eq (trim edge_s) (trim edge_p)];
  expect_opaque "desired equality cannot replace missing fact"
    (edge_eq (trim edge_s) (trim edge_p) :: without_white);
  let no_prefix_link = List.filter (fun e -> not (Expr.equal e (edge_eq edge_ph edge_h))) edge_facts in
  expect_opaque "unrelated prefix link is rejected"
    (edge_eq (slice edge_s (Expr.int 1) (Expr.int 1)) edge_h :: no_prefix_link);
  expect_opaque "interior whitespace is not trailing whitespace"
    (edge_eq (slice edge_s (Expr.int 1) (Expr.int 1)) (value [32]) :: without_white)

let edge_types_and_modes () =
  check "nonTOTAL retains symbolic trim"
    (Expr.equal (trim edge_s) (edge_reduce ~total:false (edge_gamma ()) edge_facts));
  check "unknown original input type stays opaque"
    (Expr.equal (trim edge_s) (edge_reduce (Gamma.init ()) edge_facts));
  List.iter (fun typ ->
    let g = Gamma.init () in Gamma.update g "#edge_s" typ;
    check "wrong original type keeps ordinary error"
      (try ignore (edge_reduce g edge_facts); false with
       | Reduction.ReductionException (_, msg) -> msg = "Utf16Trim requires a UTF-16 string"))
    [Type.StringType; Type.NumberType; Type.IntType; Type.ListType]

let edge_concrete_oracle_and_surrogates () =
  let reduced = edge_reduce (edge_gamma ()) edge_facts in
  List.iter (fun units ->
    let replace = Expr.subst_expr_for_expr ~to_subst:edge_s ~subst_with:(value units) in
    let evaluate e = Engine.CExprEval.evaluate_expr (store ()) (replace e) in
    check "actual concrete trim agrees before and after symbolic step"
      (Literal.equal (evaluate (trim edge_s)) (evaluate reduced)))
    [[65;32];[65;32;66;9];[0xd800;32];[0xdc00;0xfeff];
     [0xd800;0xdc00;32;0xdfff;9];[65;0;0xd800;32;32]];
  check "canonical output keeps complete original prefix"
    (Expr.equal reduced (trim edge_p))

let edge_no_repeat_or_context_mutation () =
  let g = edge_gamma () and pfs = PFS.of_list edge_facts in
  let before = PFS.copy pfs and gamma_before = gamma_pairs g in
  let old_total = !Config.Verification.total in
  Config.Verification.total := true;
  Fun.protect ~finally:(fun () -> Config.Verification.total := old_total)
    (fun () ->
      let first = Reduction.reduce_lexpr ~pfs ~gamma:g (trim edge_s) in
      let second = Reduction.reduce_lexpr ~pfs ~gamma:g first in
      check "canonical slice operand is ineligible for repeated step"
        (Expr.equal first second && Expr.equal first (trim edge_p)));
  check "repeated calls preserve PFS" (PFS.equal before pfs);
  check "repeated calls preserve gamma" (gamma_before = gamma_pairs g)

let () =
  Alcotest.run "UTF16 slice"
    ["actual bridge",
     [Alcotest.test_case "concrete and reduction" `Quick concrete_and_reduction;
      Alcotest.test_case "invalid operands" `Quick invalid_operands;
      Alcotest.test_case "actual typing paths" `Quick actual_typing_paths;
      Alcotest.test_case "actual expression syntax" `Quick expression_syntax;
      Alcotest.test_case "incoming TOTAL domains" `Quick (with_total incoming_state_domains);
      Alcotest.test_case "no executable slice or bad arity" `Quick (with_total executable_and_arity_guards);
      Alcotest.test_case "complete recursive lemma syntax" `Quick complete_lemma_syntax];

     "trim edge",
     [Alcotest.test_case "shared whitespace table full unit domain" `Quick edge_table_exhaustive;
      Alcotest.test_case "exact positive fact shapes" `Quick edge_exact_positive_facts;
      Alcotest.test_case "every missing guard" `Quick edge_every_missing_guard;
      Alcotest.test_case "bounded typed aliases and cycles" `Quick edge_one_hop_aliases;
      Alcotest.test_case "unrelated and goal-bearing facts" `Quick edge_reject_unrelated_facts;
      Alcotest.test_case "original types and TOTAL mode" `Quick edge_types_and_modes;
      Alcotest.test_case "actual concrete oracle and surrogates" `Quick edge_concrete_oracle_and_surrogates;
      Alcotest.test_case "termination and immutable context" `Quick edge_no_repeat_or_context_mutation]]
