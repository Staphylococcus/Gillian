(* Dedicated metadata attachment tests: no verifier, imports or solver run. *)
open Gillian
open Utils
open Gil_syntax
module Compiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module Parser = Gillian.Gil_parsing.Make (Annot.Basic)

let check label condition = Alcotest.(check bool) label true condition
let result = function
  | Ok value -> value
  | Error error -> Alcotest.failf "unexpected rejection: %a"
      Gillian_result.Error.pp_brief error
let parse text = result (Parser.parse_eprog_from_string text)

let import_headers () =
  let body = "\nproc header() { return };" in
  let ordinary = "import \"runtime.gil\";" in
  let verified = "import verify \"checked.gil\";" in
  let valid = [
    "no bank", "", [];
    "ordinary only", ordinary, [ "runtime.gil", false ];
    "verified only", verified, [ "checked.gil", true ];
    "ordinary then verified", ordinary ^ "\n" ^ verified,
      [ "runtime.gil", false; "checked.gil", true ];
    "multiple ordinary names", "import \"b.gil\",\"a.gil\";",
      [ "b.gil", false; "a.gil", false ];
    "multiple verified names", "import verify \"z.gil\",\"y.gil\";",
      [ "z.gil", true; "y.gil", true ];
    "multiple names in both banks",
      "import \"b.gil\",\"a.gil\";\nimport verify \"z.gil\",\"y.gil\";",
      [ "b.gil", false; "a.gil", false; "z.gil", true; "y.gil", true ] ] in
  List.iter (fun (label, header, expected) ->
      check (label ^ ": exact import names, order and verification flags")
        ((parse (header ^ body)).labeled_prog.imports = expected)) valid;
  let invalid = [
    "two ordinary banks", ordinary ^ "\n" ^ ordinary;
    "two verified banks", verified ^ "\n" ^ verified;
    "reversed banks", verified ^ "\n" ^ ordinary;
    "ordinary after both banks", ordinary ^ "\n" ^ verified ^ "\n" ^ ordinary;
    "verified after both banks", ordinary ^ "\n" ^ verified ^ "\n" ^ verified ] in
  List.iter (fun (label, header) ->
      match Parser.parse_eprog_from_string (header ^ body) with
      | Error (Gillian_result.Error.CompilationError _) -> ()
      | Error error -> Alcotest.failf "%s: expected parser compilation error, got %a"
          label Gillian_result.Error.pp_brief error
      | Ok _ -> Alcotest.fail (label ^ ": malformed import banks accepted")) invalid
let parameters = "x__scope,x__this,value,path,ancestors,copies"
let source_text = {|import "runtime.gil";
import verify "kept.gil";
pred Activation(scope:List):
  (scope == {{$lg,#er}}) * <Cell>(#er,u16"slot";undefined);
spec main() [[ emp ]] [[ (ret == empty) ]] normal
proc main() { ret := empty; return };
proc target(x__scope,x__this,value,path,ancestors,copies) {
  ret := value; return
};|}
let source () = (parse source_text).labeled_prog
let contract ?(name = "target") ?(formals = parameters) ?spec_formals
    ?(prefix = "") ?(trusted = "") ?(rank = "variant(1i)")
    ?(post = "(false) * Activation({{$lg,#er}})")
    ?(scope = "verify_scope(final_scope;{{$lg,#er}})") ?(flag = "normal")
    ?(body = "return") ?(imports = "") () =
  let spec_formals = Option.value spec_formals ~default:formals in
  Printf.sprintf "%s\n%sspec %s(%s) %s[[ emp ]] [[ %s ]] %s %s %s\nproc %s(%s) { %s };"
    imports prefix name spec_formals trusted post rank scope flag name formals body

let with_sidecar ?(suffix = ".gil") text f =
  let path = Filename.temp_file "checked-spec-overlay-" suffix in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
      let channel = open_out_bin path in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> output_string channel text);
      f path)

let load program text = with_sidecar text
    (fun path -> Compiler.load_checked_spec_overlay ~path program)

let contains text piece =
  let rec at i = i + String.length piece <= String.length text &&
    (String.sub text i (String.length piece) = piece || at (i + 1)) in
  at 0

let expect_overlay_error label reason = function
  | Error (Gillian_result.Error.CompilationError { msg; _ }) ->
      check (label ^ ": loader-specific rejection, not parser failure")
        (String.starts_with ~prefix:"Checked-spec overlay: " msg && contains msg reason)
  | Error _ -> Alcotest.fail (label ^ ": expected checked-overlay compilation error")
  | Ok _ -> Alcotest.fail ("metadata accepted: " ^ label)

let unchanged_except_specs (before : (Annot.Basic.t, string) Prog.t)
    (after : (Annot.Basic.t, string) Prog.t) targets =
  check "new procedure table, original untouched" (before.procs != after.procs);
  check "all original non-procedure tables retained as actual objects"
    (before.preds == after.preds && before.lemmas == after.lemmas &&
     before.funcs == after.funcs && before.datatypes == after.datatypes &&
     before.only_specs == after.only_specs && before.macros == after.macros &&
     before.bi_specs == after.bi_specs && before.predecessors == after.predecessors &&
     before.proc_names == after.proc_names);
  check "procedure key count preserved"
    (Hashtbl.length before.procs = Hashtbl.length after.procs);
  Hashtbl.iter (fun name (old : (Annot.Basic.t, string) Proc.t) ->
      let current = Prog.get_proc_exn after name in
      if List.mem name targets then (
        check "original target remains uncontracted" (old.proc_spec = None);
        check "target has new attached contract" (current.proc_spec <> None);
        check "all target fields except spec are original objects/flags"
          (old.proc_name == current.proc_name &&
           old.proc_source_path == current.proc_source_path &&
           old.proc_internal = current.proc_internal &&
           old.proc_body == current.proc_body && old.proc_params == current.proc_params &&
           old.proc_aliases == current.proc_aliases && old.proc_calls == current.proc_calls &&
           old.proc_display_name == current.proc_display_name &&
           old.proc_hidden = current.proc_hidden);
        Array.iteri (fun i (annotation, label, command) ->
            let a, l, c = current.proc_body.(i) in
            check "annotation (including loop info), label and command identities"
              (annotation == a && label == l && command == c)) old.proc_body)
      else check "non-target procedure retained as actual object" (old == current))
    before.procs;
  let prefix = List.filteri (fun i _ -> i < List.length before.imports) after.imports in
  check "complete original import prefix and verification flags retained"
    (prefix = before.imports)

let attach_positive () =
  let program = source () in
  let metadata = parse (contract ~imports:"import verify \"extra.gil\";" ()) in
  let expected = Option.get (Prog.get_proc_exn metadata.labeled_prog "target").proc_spec in
  let after = Compiler.attach_checked_specs metadata program in
  unchanged_except_specs program after [ "target" ];
  check "only new verified import appended"
    (after.imports = program.imports @ [ ("extra.gil", true) ]);
  let spec = Option.get (Prog.get_proc_exn after "target").proc_spec in
  check "parsed contract is attached without printing or rewriting" (spec == expected);
  match spec.spec_sspecs with
  | [ case ] ->
      check "exact native variant preserved"
        (Option.equal Expr.equal case.ss_variant (Some (Expr.int 1)));
      Spec.validate_verifier_scope ~exact_target:true case;
      check "deliberately false POST remains false"
        (List.exists (fun (post, _) -> List.exists
           (function Asrt.Pure (Expr.Lit (Literal.Bool false)) -> true | _ -> false)
           post) case.ss_posts)
  | _ -> Alcotest.fail "one complete checked case required"

let reject_metadata () =
  let controls = [
    "executable assignment", "executable stub commands", contract ~body:"ret := undefined; return" ();
    "labeled stub", "executable stub commands", contract ~body:"done: return" ();
    "incomplete", "incomplete or unchecked contract", contract ~prefix:"incomplete " ();
    "trusted case", "each case must be checked, normal and ranked", contract ~trusted:"trusted " ();
    "error case", "each case must be checked, normal and ranked", contract ~flag:"error" ();
    "missing variant", "each case must be checked, normal and ranked", contract ~rank:"" ();
    "wrong ordered formals", "ordered source formals/name mismatch", contract
      ~formals:"x__scope,x__this,value,path,copies,ancestors" ();
    "spec/procedure mismatch", "ordered source formals/name mismatch", contract ~spec_formals:"value" ();
    "unknown target", "unknown source target", contract ~name:"unknown" ();
    "existing main contract", "existing source contract", contract ~name:"main" ~formals:"" ();
    "duplicate target", "duplicate target", contract () ^ "\n" ^ contract ();
    "ordinary import", "ordinary sidecar imports are forbidden", contract ~imports:"import \"extra.gil\";" ();
    "source flag conflict", "source import verification-flag conflict", contract ~imports:"import verify \"runtime.gil\";" ();
    "duplicate original import", "duplicate source import", contract ~imports:"import verify \"kept.gil\";" ();
    "duplicate new import", "duplicate sidecar import", contract ~imports:"import verify \"extra.gil\",\"extra.gil\";" ();
    "orphan scope witness", "orphan target witness", contract ~post:"(false)" ();
    "missing entire target", "target is not the public scope expression", contract ~post:"(false) * Activation(#er)" ();
    "predicate declaration", "only checked procedure contracts", "pred Untrusted(): emp;\n" ^ contract ();
    "initialization data", "initialization data is forbidden", "#begin_init_data\n{}\n#end_init_data\n" ^ contract ();
    "axiomatic specification", "only checked procedure contracts",
      "axiomatic spec target(" ^ parameters ^ ") [[ emp ]] [[ (false) ]] variant(1i) normal" ] in
  List.iter (fun (label, reason, text) ->
      let program = source () in
      let target = Prog.get_proc_exn program "target" in
      let imports = program.imports in
      expect_overlay_error label reason (load program text);
      check (label ^ ": no target mutation")
        (Prog.get_proc_exn program "target" == target && target.proc_spec = None);
      check (label ^ ": no import mutation") (program.imports == imports)) controls;
  List.iter (fun (label, text) -> match load (source ()) text with
      | Error (Gillian_result.Error.CompilationError _) -> ()
      | Error _ | Ok _ -> Alcotest.fail (label ^ ": compilation rejection required"))
    [ "empty input", ""; "malformed syntax", "this is not GIL" ]

let reject_second_unchecked_case () =
  let text = Printf.sprintf
      "spec target(%s) [[ emp ]] [[ (false) ]] variant(1i) normal; trusted [[ emp ]] [[ (false) ]] variant(1i) normal proc target(%s) { return };"
      parameters parameters in
  expect_overlay_error "second unchecked case"
    "each case must be checked, normal and ranked" (load (source ()) text)

let reject_normalized () =
  with_sidecar ~suffix:".ngil" (contract ()) (fun path ->
      expect_overlay_error "normalized file" "requires raw .gil metadata"
        (Compiler.load_checked_spec_overlay ~path (source ())));
  let metadata = parse (contract ()) in
  let stub = Prog.get_proc_exn metadata.labeled_prog "target" in
  let spec = { (Option.get stub.proc_spec) with spec_normalised = true } in
  let procs = Hashtbl.copy metadata.labeled_prog.procs in
  Hashtbl.replace procs "target" { stub with proc_spec = Some spec };
  let metadata = { metadata with labeled_prog = { metadata.labeled_prog with procs } } in
  match (try ignore (Compiler.attach_checked_specs metadata (source ())); None
         with Invalid_argument message -> Some message) with
  | Some message -> check "normalized typed contract rejected for intended reason"
      (contains message "normalized sidecar contract")
  | None -> Alcotest.fail "normalized typed contract accepted"

let default_and_modes () =
  let program = source () in
  Compiler.checked_spec_overlay := None;
  check "absent option is exact identity" (result (Compiler.apply_checked_spec_overlay program) == program);
  with_sidecar (contract ()) (fun path ->
      let previous = !Config.current_exec_mode in
      Fun.protect ~finally:(fun () -> Config.current_exec_mode := previous)
        (fun () -> Config.current_exec_mode := Exec_mode.Symbolic;
          expect_overlay_error "non-verification mode" "requires original-JavaScript verification mode"
            (Compiler.load_checked_spec_overlay ~path program)));
  with_sidecar (contract ()) (fun path ->
      Fun.protect
        ~finally:(fun () -> Compiler.TargetLangOptions.apply
          { jsil = false; harness = false; burn_jsil = false;
            forbid_div_by_zero = false; es2015_front_end = None;
            checked_spec_overlay = None })
        (fun () ->
          Compiler.TargetLangOptions.apply
            { jsil = true; harness = false; burn_jsil = false;
              forbid_div_by_zero = false; es2015_front_end = None;
              checked_spec_overlay = Some path };
          expect_overlay_error "top-level JSIL" "non-JavaScript top-level input"
            (Compiler.parse_and_compile_files [ "not-read.jsil" ])));
  with_sidecar (contract ()) (fun path ->
      Fun.protect
        ~finally:(fun () -> Compiler.checked_spec_overlay := None; Compiler.burn_jsil := false)
        (fun () -> Compiler.checked_spec_overlay := Some path; Compiler.burn_jsil := true;
          expect_overlay_error "debug burn conflict" "cannot be combined with --burn-jsil"
            (Compiler.parse_and_compile_js "must-not-be-read.js")))

let reset_compiler () =
  let module Front = Js2jsil_lib.JS2JSIL_Compiler in
  Hashtbl.clear Front.cc_tbl;
  Hashtbl.clear Front.fun_tbl;
  Hashtbl.clear Front.old_fun_tbl;
  Hashtbl.clear Front.vis_tbl;
  Js2jsil_lib.JS2JSIL_Helpers.reset_generators ()

let actual_compiler_fixture () =
  let required name = match Sys.getenv_opt name with
    | Some path when path <> "" -> path
    | _ -> Alcotest.fail (name ^ " is required") in
  let source_path = required "GILLIAN_CHECKED_OVERLAY_SOURCE" in
  let overlay = required "GILLIAN_CHECKED_OVERLAY_FILE" in
  Compiler.checked_spec_overlay := None;
  Compiler.burn_jsil := false;
  Config.current_exec_mode := Exec_mode.Verification;
  Config.Verification.total := true;
  Compiler.initialize Exec_mode.Verification;
  reset_compiler ();
  let original, language = result (Compiler.parse_and_compile_js source_path) in
  (match language with Compiler.JavaScriptSource _ -> ()
  | Compiler.JsilSource -> Alcotest.fail "original JavaScript provenance lost");
  check "original actual Node has no assumed specification"
    ((Prog.get_proc_exn original "normalizeNode4").proc_spec = None);
  Fun.protect ~finally:(fun () -> Compiler.checked_spec_overlay := None)
    (fun () ->
      Compiler.checked_spec_overlay := Some overlay;
      let attached = result (Compiler.apply_checked_spec_overlay original) in
      unchanged_except_specs original attached [ "normalizeNode4" ];
      let spec = Option.get (Prog.get_proc_exn attached "normalizeNode4").proc_spec in
      check "both actual Node cases retained" (List.length spec.spec_sspecs = 2);
      List.iter (fun case ->
          check "actual case remains checked, normal and ranked"
            (case.Spec.ss_to_verify && case.ss_flag = Flag.Normal &&
             Option.is_some case.ss_variant);
          Spec.validate_verifier_scope ~exact_target:true case) spec.spec_sspecs;
      let compilation = Compiler.create_compilation_result source_path attached language in
      check "original JavaScript AST/provenance object retained"
        (compilation.tl_ast == language);
      let files = compilation.source_files in
      let module Sources = IncrementalAnalysis.SourceFiles in
      let paths = Sources.get_paths_set files in
      check "both original source and overlay dependency are recorded"
        (Containers.SS.mem source_path paths && Containers.SS.mem overlay paths &&
         List.mem source_path (Sources.get_dependents files ~path:overlay));
      check "both source fingerprints bind their actual files"
        (Sources.get_contents_hash files ~path:source_path = Digest.to_hex (Digest.file source_path) &&
         Sources.get_contents_hash files ~path:overlay = Digest.to_hex (Digest.file overlay));
      check "existing main contract retained as the original actual spec object"
        (Option.is_some (Prog.get_proc_exn original "main").proc_spec &&
         (Prog.get_proc_exn original "main").proc_spec ==
           (Prog.get_proc_exn attached "main").proc_spec))

(* Run ONLY metadata.006 in a separate fresh process. The compiler's private
   fresh_name counter is intentionally not reset by reset_generators; a second
   compilation in one process would change the source target's generated name.
   metadata.005 independently retains the full direct typed-identity checks. *)
let actual_compiler_option_fixture () =
  let required name = match Sys.getenv_opt name with
    | Some path when path <> "" -> path
    | _ -> Alcotest.fail (name ^ " is required") in
  let source_path = required "GILLIAN_CHECKED_OVERLAY_SOURCE" in
  let overlay = required "GILLIAN_CHECKED_OVERLAY_FILE" in
  Compiler.burn_jsil := false;
  Config.current_exec_mode := Exec_mode.Verification;
  Config.Verification.total := true;
  Compiler.initialize Exec_mode.Verification;
  reset_compiler ();
  Fun.protect ~finally:(fun () -> Compiler.checked_spec_overlay := None)
    (fun () ->
      Compiler.checked_spec_overlay := Some overlay;
      let integrated = result (Compiler.parse_and_compile_files [ source_path ]) in
      let actual = match integrated.gil_progs with
        | [ _, program ] -> program
        | _ -> Alcotest.fail "one actual original-JS program expected" in
      let node = Option.get (Prog.get_proc_exn actual "normalizeNode4").proc_spec in
      check "real compiler option installs both Node cases" (List.length node.spec_sspecs = 2);
      List.iter (fun case ->
          check "real option case remains checked, normal and ranked"
            (case.Spec.ss_to_verify && case.ss_flag = Flag.Normal &&
             Option.is_some case.ss_variant);
          Spec.validate_verifier_scope ~exact_target:true case) node.spec_sspecs;
      check "real compiler option retains existing main contract"
        (Option.is_some (Prog.get_proc_exn actual "main").proc_spec);
      (match integrated.tl_ast with Compiler.JavaScriptSource _ -> ()
       | Compiler.JsilSource -> Alcotest.fail "option hook lost JavaScript provenance");
      let module Sources = IncrementalAnalysis.SourceFiles in
      let files = integrated.source_files in
      let paths = Sources.get_paths_set files in
      check "real option retains source and sidecar provenance and dependency"
        (Containers.SS.mem source_path paths && Containers.SS.mem overlay paths &&
         List.mem source_path (Sources.get_dependents files ~path:overlay));
      check "real option fingerprints bind both actual fixture files"
        (Sources.get_contents_hash files ~path:source_path = Digest.to_hex (Digest.file source_path) &&
         Sources.get_contents_hash files ~path:overlay = Digest.to_hex (Digest.file overlay)))

let () =
  Config.current_exec_mode := Exec_mode.Verification;
  Config.Verification.total := true;
  Alcotest.run "Checked specification overlay"
    [ ("headers",
       [ Alcotest.test_case "import bank syntax, flags and ordering" `Quick import_headers ]);
      ("metadata",
       [ Alcotest.test_case "typed attachment and false POST" `Quick attach_positive;
         Alcotest.test_case "reject unsafe metadata without mutation" `Quick reject_metadata;
         Alcotest.test_case "every case must be checked" `Quick reject_second_unchecked_case;
         Alcotest.test_case "normalized metadata is forbidden" `Quick reject_normalized;
         Alcotest.test_case "default identity and mode restrictions" `Quick default_and_modes;
         Alcotest.test_case "required actual compiler fixture identity" `Quick actual_compiler_fixture;
         Alcotest.test_case "required fresh-process actual compiler option" `Quick actual_compiler_option_fixture ]) ]
