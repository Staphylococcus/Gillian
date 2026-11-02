module Filenames = struct
  (* Common *)

  let exec_mode = "exec_mode.txt"

  (* Used in verification, bi-abduction and individual symbolic testing *)

  let sources = "sources.json"
  let call_graph = "call_graph.json"
  let verif_results = "verif_results.json"
  let biabduction_results = "specs.json"

  (* Used in bulk symbolic testing *)

  let sources_dir = "sources"
  let call_graphs_dir = "call-graphs"
  let tests_ran = "tests_ran.txt"

  (* Used in tests and for debugging *)

  let diff = "diff.txt"
end

let results_dir = Config.results_dir

let prev_results_exist () =
  let results_dir = results_dir () in
  if not (Sys.file_exists results_dir && Sys.is_directory results_dir) then
    false
  else
    (* Do not use previous results if the analysis mode has changed *)
    let read_str filename =
      let file_path = Filename.concat results_dir filename in
      Io_utils.load_file file_path
    in
    let prev_exec_mode = Exec_mode.of_string (read_str Filenames.exec_mode) in
    prev_exec_mode = !Config.current_exec_mode

let delete_results_dir () = Io_utils.rm_rf (results_dir ())
let create_results_dir () = Io_utils.safe_mkdir (results_dir ())

let read_json filename =
  let json_path = Filename.concat (results_dir ()) filename in
  Yojson.Safe.from_file json_path

let read_results_dir () =
  let sources = SourceFiles.of_yojson (read_json Filenames.sources) in
  let call_graph = Call_graph.of_yojson (read_json Filenames.call_graph) in
  (Result.get_ok sources, Result.get_ok call_graph)

let read_verif_results () =
  let sources, call_graph = read_results_dir () in
  let results_json = read_json Filenames.verif_results in
  ( sources,
    call_graph,
    Result.get_ok (VerificationResults.of_yojson results_json) )

let read_biabduction_results () =
  let sources, call_graph = read_results_dir () in
  let results_json = read_json Filenames.biabduction_results in
  ( sources,
    call_graph,
    Result.get_ok (BiAbductionResults.of_yojson results_json) )

let read_symbolic_results = read_results_dir

let read_bulk_symbolic_results () =
  let read_table dirname of_json =
    let dir_path = Filename.concat (results_dir ()) dirname in
    let json_paths = Io_utils.get_files dir_path in
    let table = Hashtbl.create Config.small_tbl_size in
    let () =
      List.iter
        (fun path ->
          let test_name = Filename.basename (Filename.chop_extension path) in
          let json = Yojson.Safe.from_file path in
          Hashtbl.add table test_name (of_json json))
        json_paths
    in
    table
  in
  let source_files =
    read_table Filenames.sources_dir (fun x ->
        Result.get_ok (SourceFiles.of_yojson x))
  in
  let call_graphs =
    read_table Filenames.call_graphs_dir (fun x ->
        Result.get_ok (Call_graph.of_yojson x))
  in
  (source_files, call_graphs)

let write_json json ?dirname filename =
  let dir_path =
    Option.fold ~none:(results_dir ())
      ~some:(fun dirname ->
        let dir_path = Filename.concat (results_dir ()) dirname in
        Io_utils.safe_mkdir dir_path;
        dir_path)
      dirname
  in
  let json_path = Filename.concat dir_path filename in
  let channel = open_out json_path in
  Yojson.Safe.pretty_to_channel channel json;
  close_out channel

let write_str str filename =
  let out_path = Filename.concat (results_dir ()) filename in
  let channel = open_out out_path in
  Printf.fprintf channel "%s" str;
  close_out channel

let write_results_dir sources call_graph ~diff =
  delete_results_dir ();
  create_results_dir ();
  write_json (SourceFiles.to_yojson sources) Filenames.sources;
  write_json (Call_graph.to_yojson call_graph) Filenames.call_graph;
  write_str (Exec_mode.to_string !Config.current_exec_mode) Filenames.exec_mode;
  write_str diff Filenames.diff

let write_verif_results sources call_graph ~diff results =
  let results_json = VerificationResults.to_yojson results in
  write_results_dir sources call_graph ~diff;
  write_json results_json Filenames.verif_results

(* This opt-in observation is deliberately separate from the reusable cache. *)
let write_closed_entry_observation ~closed_entry ~path results =
  if closed_entry then
    match path with
    | None | Some "" -> ()
    | Some path ->
        if Filename.is_relative path then
          invalid_arg "closed-entry observation path must be absolute";
        let body =
          Yojson.Safe.to_string
            (`Assoc
              [
                ("format", `String "gillian-closed-entry-results-v1");
                ("mode", `String "closed-entry");
                ("reusable", `Bool false);
                ("results", VerificationResults.to_yojson results);
              ])
          ^ "\n"
        in
        if String.length body > 1024 * 1024 then
          invalid_arg "closed-entry observation exceeds 1 MiB";
        let canonical_parent path =
          let parent = Unix.realpath (Filename.dirname path) in
          if (Unix.stat parent).Unix.st_kind <> Unix.S_DIR then
            invalid_arg "closed-entry observation parent must be a directory";
          parent
        in
        let basename = Filename.basename path in
        if basename = "." || basename = ".." then
          invalid_arg "closed-entry observation path must name a file";
        let destination = Filename.concat (canonical_parent path) basename in
        let cache = results_dir () in
        let cache_exists =
          try
            ignore (Unix.lstat cache);
            true
          with Unix.Unix_error (Unix.ENOENT, _, _) -> false
        in
        let cache =
          if cache_exists then (
            let cache = Unix.realpath cache in
            if (Unix.stat cache).Unix.st_kind <> Unix.S_DIR then
              invalid_arg "closed-entry reusable cache must be a directory";
            cache)
          else Filename.concat (canonical_parent cache) (Filename.basename cache)
        in
        let cache_prefix = if cache = "/" then cache else cache ^ "/" in
        if
          String.equal destination cache
          || String.starts_with ~prefix:cache_prefix destination
        then
          invalid_arg "closed-entry observation must be outside reusable cache";
        let fd =
          Unix.openfile destination
            [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL; Unix.O_CLOEXEC ]
            0o600
        in
        Fun.protect
          ~finally:(fun () -> Unix.close fd)
          (fun () ->
            Unix.fchmod fd 0o600;
            let identity = Unix.fstat fd in
            if
              identity.Unix.st_kind <> Unix.S_REG
              || identity.Unix.st_nlink <> 1
              || identity.Unix.st_perm <> 0o600
            then failwith "closed-entry observation is not a fresh private file";
            let rec write_all offset =
              if offset < String.length body then
                match
                  Unix.write_substring fd body offset
                    (String.length body - offset)
                with
                | 0 -> failwith "closed-entry observation write made no progress"
                | written -> write_all (offset + written)
                | exception Unix.Unix_error (Unix.EINTR, _, _) -> write_all offset
            in
            write_all 0;
            Unix.fsync fd)

let write_biabduction_results sources call_graph ~diff results =
  let results_json = BiAbductionResults.to_yojson results in
  write_results_dir sources call_graph ~diff;
  write_json results_json Filenames.biabduction_results

let write_symbolic_results = write_results_dir

let write_bulk_symbolic_results ~tests_ran sources_table call_graph_table =
  let write_str_list str_list filename =
    let out_path = Filename.concat (results_dir ()) filename in
    let channel = open_out out_path in
    let fmt = Format.formatter_of_out_channel channel in
    let newline = Fmt.any "@\n" in
    Fmt.pf fmt "%a@?" (Fmt.list ~sep:newline Fmt.string) str_list;
    close_out channel
  in
  let write_table table dirname to_json =
    Hashtbl.iter
      (fun test_name results ->
        write_json (to_json results) ~dirname (test_name ^ ".json"))
      table
  in
  delete_results_dir ();
  create_results_dir ();
  write_str_list tests_ran Filenames.tests_ran;
  write_table sources_table Filenames.sources_dir SourceFiles.to_yojson;
  write_table call_graph_table Filenames.call_graphs_dir Call_graph.to_yojson;
  write_str (Exec_mode.to_string !Config.current_exec_mode) Filenames.exec_mode
