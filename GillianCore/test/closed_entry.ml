module V = Gillian.Utils.Config.Verification

exception Expected

let phase_scope () =
  let saved = !V.closed_entry_heap_abstracted in
  Fun.protect
    ~finally:(fun () -> V.closed_entry_heap_abstracted := saved)
    (fun () ->
      List.iter
        (fun previous ->
          V.closed_entry_heap_abstracted := previous;
          let check label expected =
            Alcotest.(check bool) label expected !V.closed_entry_heap_abstracted
          in
          let execute () =
            check "new invocation starts before abstraction" false;
            V.closed_entry_heap_abstracted := true;
            check "abstraction persists within invocation" true
          in
          V.with_fresh_closed_entry_heap_phase execute;
          check "success restores the previous scope" previous;
          Alcotest.check_raises "exception escapes after restoring scope"
            Expected (fun () ->
              V.with_fresh_closed_entry_heap_phase (fun () ->
                  execute ();
                  raise Expected));
          check "exception restores the previous scope" previous;
          V.with_fresh_closed_entry_heap_phase (fun () ->
              check "next invocation also starts before abstraction" false);
          check "next invocation restores its caller" previous)
        [ false; true ])

module Results = Gillian.IncrementalAnalysis.VerificationResults
module Results_dir = Gillian.IncrementalAnalysis.ResultsDir

let with_temp_directory f =
  let root = Filename.temp_file "gillian-closed-observation-" "" in
  Sys.remove root;
  Unix.mkdir root 0o700;
  let rec remove_owned path =
    if (Unix.lstat path).Unix.st_kind = Unix.S_DIR then (
      Array.iter
        (fun name -> remove_owned (Filename.concat path name))
        (Sys.readdir path);
      Unix.rmdir path)
    else Unix.unlink path
  in
  Fun.protect ~finally:(fun () -> remove_owned root) (fun () -> f root)

let read_file path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      really_input_string channel (in_channel_length channel))

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () ->
      output_string channel contents)

let expect_unix_error label expected f =
  let actual =
    try
      f ();
      None
    with Unix.Unix_error (error, _, _) -> Some error
  in
  Alcotest.(check bool) label true (actual = Some expected)

let absent path =
  try
    ignore (Unix.lstat path);
    false
  with Unix.Unix_error (Unix.ENOENT, _, _) -> true

let cache_snapshot () =
  let root = Gillian.Utils.Config.results_dir () in
  List.map
    (fun path ->
      let identity =
        try Some (Unix.lstat path) with
        | Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> None
      in
      (path, identity))
    (root
    :: List.map (Filename.concat root)
         [
           "sources.json";
           "call_graph.json";
           "exec_mode.txt";
           "verif_results.json";
           "diff.txt";
         ])

let sample_results () =
  let results = Results.make () in
  Results.set_result results "main" (0, 0) true;
  Results.set_result results "main" (0, 1) false;
  Results.set_result results "auxiliary" (2, 3) true;
  results

let observation_round_trip () =
  with_temp_directory (fun root ->
      let path = Filename.concat root "observation.json" in
      let results = sample_results () in
      let expected = Results.to_yojson results in
      let cache_before = cache_snapshot () in
      Results_dir.write_closed_entry_observation ~closed_entry:true
        ~path:(Some path) results;
      let raw = read_file path in
      Alcotest.(check bool) "serialized newline" true
        (String.length raw > 0 && raw.[String.length raw - 1] = '\n');
      let fields =
        match Yojson.Safe.from_string raw with
        | `Assoc fields -> fields
        | _ -> Alcotest.fail "observation envelope must be an object"
      in
      Alcotest.(check int) "exact envelope field count" 4 (List.length fields);
      let field name = List.assoc name fields in
      Alcotest.(check bool) "format" true
        (field "format" = `String "gillian-closed-entry-results-v1");
      Alcotest.(check bool) "mode" true (field "mode" = `String "closed-entry");
      Alcotest.(check bool) "explicit non-reusability" true
        (field "reusable" = `Bool false);
      Alcotest.(check bool) "actual result JSON unchanged" true
        (field "results" = expected);
      let restored =
        match Results.of_yojson (field "results") with
        | Ok restored -> restored
        | Error error -> Alcotest.fail error
      in
      let rows = function
        | `List rows -> List.sort Stdlib.compare rows
        | _ -> Alcotest.fail "result rows must be a list"
      in
      Alcotest.(check bool) "real result decoder round trip" true
        (rows expected = rows (Results.to_yojson restored));
      Alcotest.(check bool) "false normalized row retained" true
        (List.mem
           (`List
             [ `List [ `String "main"; `List [ `Int 0; `Int 1 ] ]; `Bool false ])
           (rows (field "results")));
      Alcotest.(check bool) "in-memory results unchanged" true
        (Results.to_yojson results = expected);
      let identity = Unix.lstat path in
      Alcotest.(check bool) "regular observation" true
        (identity.Unix.st_kind = Unix.S_REG);
      Alcotest.(check int) "private mode" 0o600 identity.Unix.st_perm;
      Alcotest.(check int) "single link" 1 identity.Unix.st_nlink;
      Alcotest.(check bool) "ordinary cache untouched" true
        (cache_snapshot () = cache_before))

let observation_disabled () =
  with_temp_directory (fun root ->
      let path = Filename.concat root "disabled.json" in
      let results = sample_results () in
      let before = Results.to_yojson results in
      let cache_before = cache_snapshot () in
      Results_dir.write_closed_entry_observation ~closed_entry:true ~path:None
        results;
      Results_dir.write_closed_entry_observation ~closed_entry:true ~path:(Some "")
        results;
      Results_dir.write_closed_entry_observation ~closed_entry:false
        ~path:(Some path) results;
      Results_dir.write_closed_entry_observation ~closed_entry:false
        ~path:(Some "relative-disabled.json") results;
      Alcotest.(check bool) "disabled modes create no file" true (absent path);
      Alcotest.(check bool) "disabled modes preserve results" true
        (Results.to_yojson results = before);
      Alcotest.(check bool) "disabled modes preserve cache" true
        (cache_snapshot () = cache_before))

let observation_absolute_path () =
  Alcotest.check_raises "relative path refused"
    (Invalid_argument "closed-entry observation path must be absolute")
    (fun () ->
      Results_dir.write_closed_entry_observation ~closed_entry:true
        ~path:(Some "relative-observation.json") (sample_results ()))

let observation_cache_boundary () =
  with_temp_directory (fun root ->
      let cache_before = cache_snapshot () in
      let cache = Gillian.Utils.Config.results_dir () in
      let absolute =
        try Unix.realpath cache with
        | Unix.Unix_error (Unix.ENOENT, _, _) ->
            if Filename.is_relative cache then
              Filename.concat (Sys.getcwd ()) cache
            else cache
      in
      let refuse label path =
        Alcotest.check_raises label
          (Invalid_argument
             "closed-entry observation must be outside reusable cache")
          (fun () ->
            Results_dir.write_closed_entry_observation ~closed_entry:true
              ~path:(Some path) (sample_results ()))
      in
      refuse "cache root refused even when not yet present" absolute;
      let alias = Filename.concat root "cache-parent-alias" in
      Unix.symlink (Filename.dirname absolute) alias;
      refuse "canonical parent alias to cache refused"
        (Filename.concat alias (Filename.basename absolute));
      Alcotest.(check bool) "cache guard never creates or changes cache" true
        (cache_snapshot () = cache_before))

let observation_existing_file () =
  with_temp_directory (fun root ->
      let path = Filename.concat root "existing.json" in
      write_file path "unchanged sentinel";
      expect_unix_error "existing file refused" Unix.EEXIST (fun () ->
          Results_dir.write_closed_entry_observation ~closed_entry:true
            ~path:(Some path) (sample_results ()));
      Alcotest.(check string) "existing bytes intact" "unchanged sentinel"
        (read_file path))

let observation_symlink () =
  with_temp_directory (fun root ->
      let target = Filename.concat root "sentinel" in
      let path = Filename.concat root "symlink.json" in
      write_file target "symlink target unchanged";
      Unix.symlink target path;
      expect_unix_error "destination symlink refused" Unix.EEXIST (fun () ->
          Results_dir.write_closed_entry_observation ~closed_entry:true
            ~path:(Some path) (sample_results ()));
      Alcotest.(check string) "symlink intact" target (Unix.readlink path);
      Alcotest.(check string) "target bytes intact" "symlink target unchanged"
        (read_file target))

let observation_missing_parent () =
  with_temp_directory (fun root ->
      let parent = Filename.concat root "missing-parent" in
      let path = Filename.concat parent "observation.json" in
      expect_unix_error "missing parent refused" Unix.ENOENT (fun () ->
          Results_dir.write_closed_entry_observation ~closed_entry:true
            ~path:(Some path) (sample_results ()));
      Alcotest.(check bool) "missing parent not created" true (absent parent))

let observation_size_bound () =
  with_temp_directory (fun root ->
      let path = Filename.concat root "oversized.json" in
      let results = Results.make () in
      Results.set_result results (String.make (1024 * 1024) 'x') (0, 0) false;
      Alcotest.check_raises "full envelope capped before open"
        (Invalid_argument "closed-entry observation exceeds 1 MiB") (fun () ->
          Results_dir.write_closed_entry_observation ~closed_entry:true
            ~path:(Some path) results);
      Alcotest.(check bool) "oversized observation creates no file" true
        (absent path))

let final_local_exports () =
  let open Gillian.Gil_syntax in
  let a = Expr.LVar "#outer" and b = Expr.LVar "#discarded" in
  let public = [([Asrt.pred "Owners" [a;b] []],None)] in
  let case = Spec.s_init ([Asrt.Emp],None) public None Flag.Normal true in
  let bindings = [
    Spec.{vsb_source=Expr.PVar "allocated";vsb_target=a};
    Spec.{vsb_source=Expr.PVar "old_exports";vsb_target=b}] in
  Spec.validate_final_locals case bindings;
  Alcotest.(check bool) "public posts unchanged" true (case.ss_posts=public);
  let private_posts=Spec.final_local_posts bindings public in
  Alcotest.(check int) "two checked equalities" 3 (List.length(fst(List.hd private_posts)));
  Alcotest.(check bool) "exact value identity" true
    (List.for_all (function Asrt.Pure(Expr.BinOp(_,ValueEqual,_))->true|_->false)
      (List.filteri(fun i _->i<2)(fst(List.hd private_posts))));
  Alcotest.(check bool) "only existing final bindings accepted" true
    (Result.is_ok(Spec.require_final_local_sources bindings
       ~mem:(fun x->x="allocated"||x="old_exports")));
  Alcotest.(check bool) "missing final source fails" true
    (Result.is_error(Spec.require_final_local_sources bindings
       ~mem:(fun x->x="allocated")));
  let reject case bindings =
    match (try Spec.validate_final_locals case bindings;None
           with Invalid_argument why->Some why) with
    |Some _->()
    |None->Alcotest.fail "invalid final-local binding accepted" in
  let first=List.hd bindings in
  List.iter(fun bindings->reject case bindings)[
    [first;first];
    [{first with vsb_source=Expr.LVar "#forged"}];
    [{first with vsb_target=Expr.PVar "not_logical"}]];
  reject {case with ss_pre=([Asrt.Pure(Expr.BinOp(a,Equal,a))],None)} bindings;
  reject {case with ss_posts=[]} bindings;
  reject {case with ss_posts=public@[([Asrt.Emp],None)]} bindings;
  reject {case with ss_to_verify=false} bindings;
  reject {case with ss_flag=Flag.Error} bindings;
  reject {case with ss_verifier_scope=Some Spec.{
    vsb_source=Expr.PVar "scope";vsb_target=Expr.EList[b]}} bindings

let tests =
  [
    Alcotest.test_case "heap phase scope" `Quick phase_scope;
    Alcotest.test_case "checked final local exports" `Quick final_local_exports;
    Alcotest.test_case "closed observation round trip" `Quick
      observation_round_trip;
    Alcotest.test_case "closed observation disabled modes" `Quick
      observation_disabled;
    Alcotest.test_case "closed observation absolute path" `Quick
      observation_absolute_path;
    Alcotest.test_case "closed observation cache boundary" `Quick
      observation_cache_boundary;
    Alcotest.test_case "closed observation existing file" `Quick
      observation_existing_file;
    Alcotest.test_case "closed observation symlink" `Quick observation_symlink;
    Alcotest.test_case "closed observation missing parent" `Quick
      observation_missing_parent;
    Alcotest.test_case "closed observation size bound" `Quick
      observation_size_bound;
  ]
