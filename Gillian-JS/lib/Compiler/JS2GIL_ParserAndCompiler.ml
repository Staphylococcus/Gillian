open Cmdliner

let burn_jsil = ref false
let checked_spec_overlay : string option ref = ref None

module TargetLangOptions = struct
  type t = {
    jsil : bool;
    harness : bool;
    burn_jsil : bool;
    forbid_div_by_zero : bool;
    es2015_front_end : string option;
    checked_spec_overlay : string option;
  }

  let term =
    let docs = Manpage.s_common_options in
    let doc = "If the target language is JSIL instead of JS" in
    let jsil = Arg.(value & flag & info [ "jsil"; "from-jsil" ] ~docs ~doc) in
    let doc = "Enable ES6 harness" in
    let harness = Arg.(value & flag & info [ "harness" ] ~docs ~doc) in
    let doc = "If you want to write the intermediate JSIL file" in
    let burn_jsil = Arg.(value & flag & info [ "burn-jsil" ] ~docs ~doc) in
    let doc =
      "Treat division and modulo by zero as a runtime error. Division by zero \
       is well-defined in JavaScript (it yields Infinity/NaN); this flag makes \
       it raise an error instead, which is useful for bug-finding."
    in
    let forbid_div_by_zero =
      Arg.(value & flag & info [ "forbid-div-by-zero" ] ~docs ~doc)
    in
    let doc =
      "Opt in to a pinned ES2015 Babel frontend profile before ES5 parsing. \
       The stored input source is preserved; compiler derivatives and source \
       maps are retained by the profile's bridge."
    in
    let es2015_front_end =
      Arg.(value & opt (some string) None & info [ "es2015-front-end" ] ~docs ~doc)
    in
    let doc =
      "Attach checked procedure specifications from a metadata-only GIL sidecar \
       to the actual original-JavaScript typed program (verification only)."
    in
    let overlay =
      Arg.(value & opt (some string) None & info [ "checked-spec-overlay" ] ~docs ~doc)
    in
    let f jsil harness burn_jsil forbid_div_by_zero es2015_front_end checked_spec_overlay =
      { jsil; harness; burn_jsil; forbid_div_by_zero; es2015_front_end; checked_spec_overlay }
    in
    Term.(const f $ jsil $ harness $ burn_jsil $ forbid_div_by_zero $ es2015_front_end $ overlay)

  let apply
      { jsil; harness; burn_jsil = conf_burn_jsil; forbid_div_by_zero;
        es2015_front_end; checked_spec_overlay = overlay } =
    burn_jsil := conf_burn_jsil;
    Javert_utils.Js_config.js := not jsil;
    Javert_utils.Js_config.js2jsil_harnessing := harness;
    Javert_utils.Js_config.forbid_div_by_zero := forbid_div_by_zero;
    ES2015Frontend.profile := es2015_front_end;
    checked_spec_overlay := overlay
end

type init_data = unit
type err = JSParserErr of JS_Parser.Error.t | JS2GILErr of string
type tl_ast = JavaScriptSource of JS_Parser.Syntax.exp | JsilSource

module Annot = Gil_syntax.Annot.Basic

module CheckedSpecParser = Gillian.Gil_parsing.Make (Annot)

let overlay_error message =
  Gillian_result.compilation_error ("Checked-spec overlay: " ^ message)

(* Only attached contracts and new verified import names may come from the
   sidecar. Its one-command procedure stubs are syntax containers, never code. *)
let attach_checked_specs
    (metadata : CheckedSpecParser.parsing_result)
    (prog : (Annot.t, string) Gil_syntax.Prog.t) =
  let open Gil_syntax in
  let reject message = invalid_arg message in
  if not (Exec_mode.is_verification_exec !Config.current_exec_mode) then
    reject "requires original-JavaScript verification mode";
  let sidecar = metadata.labeled_prog in
  if metadata.init_data <> `Null then reject "initialization data is forbidden";
  if List.exists (( <> ) 0)
      [ Hashtbl.length sidecar.preds; Hashtbl.length sidecar.lemmas;
        Hashtbl.length sidecar.macros; Hashtbl.length sidecar.only_specs;
        Hashtbl.length sidecar.funcs; Hashtbl.length sidecar.datatypes;
        Hashtbl.length sidecar.bi_specs; Hashtbl.length sidecar.predecessors ]
  then reject "only checked procedure contracts and verified imports are allowed";
  if Hashtbl.length sidecar.procs = 0 then reject "at least one target is required";
  let seen = Hashtbl.create (Hashtbl.length sidecar.procs) in
  let updates = ref [] in
  Hashtbl.iter (fun name (stub : (Gil_syntax.Annot.Basic.t, string) Proc.t) ->
      if Hashtbl.mem seen name then reject ("duplicate target " ^ name);
      Hashtbl.add seen name ();
      (match stub.proc_body with
      | [| _, None, Cmd.ReturnNormal |] -> ()
      | _ -> reject ("target " ^ name ^ " contains executable stub commands"));
      if stub.proc_internal then reject ("internal sidecar target " ^ name);
      let target = match Prog.get_proc prog name with
        | Some target -> target
        | None -> reject ("unknown source target " ^ name) in
      if target.proc_name <> name || stub.proc_name <> name then
        reject "target name mismatch";
      if target.proc_spec <> None then reject ("existing source contract " ^ name);
      let spec = match stub.proc_spec with
        | Some spec -> spec
        | None -> reject ("missing checked contract " ^ name) in
      if spec.spec_name <> name || stub.proc_params <> target.proc_params ||
         spec.spec_params <> target.proc_params then
        reject ("ordered source formals/name mismatch " ^ name);
      if spec.spec_normalised then reject ("normalized sidecar contract " ^ name);
      if spec.spec_incomplete || not spec.spec_to_verify || spec.spec_sspecs = [] then
        reject ("incomplete or unchecked contract " ^ name);
      List.iter (fun case ->
          if not case.Spec.ss_to_verify || case.ss_flag <> Flag.Normal ||
             Option.is_none case.ss_variant then
            reject ("each case must be checked, normal and ranked: " ^ name);
          Spec.validate_verifier_scope ~exact_target:true case) spec.spec_sspecs;
      updates := (name, target, spec) :: !updates) sidecar.procs;
  let import_names = Hashtbl.create (List.length sidecar.imports) in
  List.iter (fun (name, verify) ->
      if not verify then reject "ordinary sidecar imports are forbidden";
      if Hashtbl.mem import_names name then reject ("duplicate sidecar import " ^ name);
      Hashtbl.add import_names name ();
      match List.assoc_opt name prog.imports with
      | None -> ()
      | Some old_flag -> reject ((if old_flag then "duplicate source import "
          else "source import verification-flag conflict ") ^ name)) sidecar.imports;
  (* Validation above is complete before any candidate output is constructed.
     All original tables/commands/annotations and non-target records are shared. *)
  let procs = Hashtbl.copy prog.procs in
  List.iter (fun (name, target, spec) ->
      Hashtbl.replace procs name { target with Proc.proc_spec = Some spec }) !updates;
  { prog with procs; imports = prog.imports @ sidecar.imports }

let load_checked_spec_overlay ~path prog =
  if Filename.extension path <> ".gil" then
    overlay_error "requires raw .gil metadata, not normalized or other input"
  else if not (Exec_mode.is_verification_exec !Config.current_exec_mode) then
    overlay_error "requires original-JavaScript verification mode"
  else
    try
      let previous = !Config.previously_normalised in
      let parsed = Fun.protect
          ~finally:(fun () -> Config.previously_normalised := previous)
          (fun () -> CheckedSpecParser.parse_eprog_from_file path) in
      match parsed with
      | Error error -> Error error
      | Ok metadata -> Ok (attach_checked_specs metadata prog)
    with Invalid_argument message | Sys_error message | Failure message ->
      overlay_error message

let apply_checked_spec_overlay prog =
  match !checked_spec_overlay with
  | None -> Ok prog
  | Some path -> load_checked_spec_overlay ~path prog

let pp_err fmt = function
  | JS2GILErr s -> Fmt.pf fmt "%s" s
  | JSParserErr s -> Fmt.pf fmt "Parsing error: %s\n" (JS_Parser.Error.str s)

let create_compilation_result path prog tl_prog =
  let open Command_line.ParserAndCompiler in
  let open IncrementalAnalysis in
  let source_files = SourceFiles.make () in
  (* TODO (Alexis): Track any require()'d modules *)
  let () = SourceFiles.add_source_file source_files ~path in
  let () = Option.iter (fun overlay ->
      SourceFiles.add_source_file source_files ~path:overlay;
      SourceFiles.add_dependency source_files ~path:overlay ~dependent_path:path)
      !checked_spec_overlay in
  let gil_path = Filename.chop_extension path ^ ".gil" in
  {
    gil_progs = [ (gil_path, prog) ];
    source_files;
    tl_ast = tl_prog;
    init_data = ();
  }

let parse_and_compile_js path =
  if Option.is_some !checked_spec_overlay && !burn_jsil then
    overlay_error "cannot be combined with --burn-jsil"
  else if Option.is_some !checked_spec_overlay &&
     not (Exec_mode.is_verification_exec !Config.current_exec_mode) then
    overlay_error "requires original-JavaScript verification mode"
  else try
    let e_str = Javert_utils.Io_utils.load_js_file path in
    let e_str =
      if !Javert_utils.Js_config.cosette then
        JS_PreParser.stringify_assume_and_assert e_str
      else e_str
    in
    let e_str = ES2015Frontend.transform ~path e_str in
    let js_prog = JS_Parser.parse_string_exn ~program_path:path e_str in
    let (ext_prog : Jsil_syntax.EProg.t), _, _ =
      JS2JSIL_Compiler.js2jsil ~filename:path js_prog
        (Exec_mode.is_verification_exec !Config.current_exec_mode)
    in
    let ext_prog =
      if !Config.unfolding then JSIL_PostParser.post_parse_eprog ext_prog
      else ext_prog
    in
    let ext_prog =
      if Exec_mode.is_biabduction_exec !Config.current_exec_mode then
        JSIL_PostParser.bi_post_parse_eprog ext_prog JS2JSIL_Compiler.cc_tbl
          JS2JSIL_Compiler.vis_tbl
      else ext_prog
    in
    let () =
      if !burn_jsil then
        let jsil_file_name = Filename.chop_extension path ^ ".jsil" in

        Io_utils.save_file_pp jsil_file_name Jsil_syntax.EProg.pp ext_prog
    in
    let core_prog = JSIL2GIL.jsil2core_prog ext_prog in
    Result.map (fun program -> (program, JavaScriptSource js_prog))
      (apply_checked_spec_overlay core_prog)
  with
  | ES2015Frontend.Frontend_error message ->
      Gillian_result.compilation_error message
  | JS_Parser.Error.ParserError e ->
      let msg = Fmt.str "Parsing error: %s\n" (JS_Parser.Error.str e) in
      let additional_data = `Assoc [ ("is_parser_error", `Bool true) ] in
      Gillian_result.compilation_error ~additional_data msg
  | JS2JSIL_Preprocessing.EarlyError e ->
      let msg =
        Fmt.str "\nParser post-processing threw an EarlyError: %s\n" e
      in
      Gillian_result.compilation_error msg

(*
  | _ ->
      Error
        (JS2GILErr
           (Printf.sprintf "\nParsing problems with the file '%s'\n" path))
  *)

let parse_and_compile_jsil path =
  let jsil_prog = Parsing.parse_jsil_eprog_from_file path in
  let core_prog = JSIL2GIL.jsil2core_prog jsil_prog in
  Ok core_prog

let parse_and_compile_files paths =
  let path = List.hd paths in
  let progs =
    if Option.is_some !checked_spec_overlay && not !Javert_utils.Js_config.js then
      overlay_error "is not supported for a non-JavaScript top-level input"
    else if !Javert_utils.Js_config.js then parse_and_compile_js path
    else Result.map (fun cp -> (cp, JsilSource)) (parse_and_compile_jsil path)
  in
  Result.map
    (fun (core_prog, tl_prog) ->
      create_compilation_result path core_prog tl_prog)
    progs

let other_imports = [ ("jsil", parse_and_compile_jsil) ]
let import_paths = Javert_utils.Js_config.import_paths
let default_import_paths = Some Runtime_sites.Sites.runtime

let initialize exec_mode =
  let open Exec_mode in
  Config.lemma_proof := false;
  Javert_utils.Js_config.cosette :=
    is_biabduction_exec exec_mode || is_symbolic_exec exec_mode;
  if is_concrete_exec exec_mode then Config.unfolding := false
