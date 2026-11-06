let test_suites : unit Alcotest.test list =
  [
    ("Gil_syntax.Reducers", Gil_syntax_tests.Visitors.tests);
    ("Binary64", Numeric.tests);
    ("Literal equality", Literal_equality.tests);
    ("List heads", List_heads.tests);
    ("List indices", List_indices.tests);
    ("Boolean integer", Boolean_integer.tests);
    ("Closed entry", Closed_entry.tests);
    ("Strings", Strings.tests);
    ("UTF-16 bridge", Utf16_bridge.tests);
    ("UTF-16 values", Utf16_values.tests);
    ("Sufficient entailment", Entailment.tests);
    ("Predicate matching", Predicate_matching.tests);
    ("Assertion domains", Assertion_domains.tests);
    ("Linked program capture", Linked_program_capture.tests);
    ("List normalization", List_normalization.tests);
    ("Owned prefix lifecycle", Owned_prefix_lifecycle.tests);
  ]

let () =
  let wrap_up_logging =
    match Sys.getenv_opt "GILLIAN_NATIVE_SMT_CONTEXT_DIR" with
    | None -> (fun () -> ())
    | Some _ ->
        let module L = Logging in
        Gillian.Utils.Config.dump_smt := true;
        L.Mode.set_mode (Enabled Normal);
        L.initialize [L.file_reporter];
        L.wrap_up
  in
  at_exit (fun () ->
      Fun.protect ~finally:wrap_up_logging Smt.shutdown_solver)

(* Opt-in lifecycle controls; without this variable the original Alcotest
   registry, selection and assertions run unchanged. Every recognized probe
   first submits a real native UNSAT query; printed markers are not verdicts
   for process closure, which must be checked by the external lifecycle guard. *)
(* This isolated probe owns only its native solver child. ECHILD is the only
   passing observation: a live child, or one reaped here instead of by shutdown,
   is a control failure. Do not turn a successful waitpid into cleanup credit. *)
let assert_terminal_solver_reaped stage =
  try
    let pid, _ = Unix.waitpid [Unix.WNOHANG] (-1) in
    failwith
      (if pid = 0 then
         "SMT terminal probe " ^ stage ^ ": child still live"
       else
         Printf.sprintf "SMT terminal probe %s: probe reaped child %d" stage pid)
  with
  | Unix.Unix_error (Unix.ECHILD, _, _) ->
      Printf.printf "SMT_TERMINAL_PROBE no-children=%s\n%!" stage

let terminal_probe_read_file path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> In_channel.input_all channel)

let observe_terminal_solver_child () =
  let parent = Unix.getpid () in
  let children_path = Printf.sprintf "/proc/self/task/%d/children" parent in
  let children () =
    terminal_probe_read_file children_path |> String.trim
    |> String.split_on_char ' '
    |> List.filter (fun value -> value <> "")
    |> List.map int_of_string
  in
  let child =
    match children () with
    | [pid] when pid > 0 -> pid
    | _ -> failwith "SMT terminal probe expected exactly one direct solver child"
  in
  let proc_path = Printf.sprintf "/proc/%d" child in
  let argv =
    terminal_probe_read_file (proc_path ^ "/cmdline")
    |> String.split_on_char '\000'
    |> List.filter (fun value -> value <> "")
  in
  let executable = Unix.readlink (proc_path ^ "/exe") in
  let status =
    terminal_probe_read_file (proc_path ^ "/status") |> String.split_on_char '\n'
  in
  let parent_line = List.find (String.starts_with ~prefix:"PPid:") status in
  let actual_parent =
    String.sub parent_line 5 (String.length parent_line - 5)
    |> String.trim |> int_of_string
  in
  if argv <> ["z3"; "-in"; "-smt2"] || executable <> "/usr/bin/z3"
     || actual_parent <> parent || children () <> [child] then
    failwith "SMT terminal probe direct child identity changed or is not Z3";
  Printf.printf
    "SMT_TERMINAL_PROBE owned-child pid=%d ppid=%d argv=z3,-in,-smt2 exe=%S\n%!"
    child actual_parent executable

let terminal_solver_probe mode =
  let () =
    match mode with
    | "normal" | "close-twice-gc" | "uncaught-exception" | "postshutdown-io" -> ()
    | _ -> invalid_arg ("Unknown GILLIAN_SMT_TERMINAL_PROBE mode: " ^ mode)
  in
  let open Gillian.Gil_syntax in
  let fs = Expr.Set.singleton (Expr.Lit (Literal.Bool false)) in
  let gamma = Hashtbl.create 1 in
  (match Smt.exec_sat ~caller_kind:"terminal-solver-probe" fs gamma with
  | None -> print_endline "SMT_TERMINAL_PROBE native=UNSAT"
  | Some _ -> failwith "SMT terminal probe expected actual native UNSAT");
  observe_terminal_solver_child ();
  match mode with
  | "normal" -> print_endline "SMT_TERMINAL_PROBE body=normal"
  | "close-twice-gc" ->
      Smt.shutdown_solver ();
      assert_terminal_solver_reaped "after-first-close";
      Gc.full_major ();
      Smt.shutdown_solver ();
      assert_terminal_solver_reaped "after-gc-second-close";
      print_endline "SMT_TERMINAL_PROBE explicit-close-twice-gc=returned"
  | "uncaught-exception" ->
      failwith "SMT_TERMINAL_PROBE_EXPECTED_UNCAUGHT"
  | "postshutdown-io" ->
      Smt.shutdown_solver ();
      let rejected =
        try
          ignore
            (Smt.exec_sat ~caller_kind:"terminal-solver-probe-rejected" fs gamma);
          false
        with
        | Smt.SMT_error message
          when String.equal message "SMT solver is terminally shut down" -> true
      in
      if not rejected then failwith "SMT terminal probe allowed post-shutdown I/O";
      print_endline "SMT_TERMINAL_PROBE postshutdown-io=rejected"
  | _ -> assert false

let () =
  match Sys.getenv_opt "GILLIAN_REQUIRED_UNKNOWN_REPLAY" with
  | Some path ->
      let result = Smt.replay_required_unknown_input path in
      Printf.printf "SMT_NEEDED_INPUT_REPLAY result=%s checks=1 proof=false\n%!" result
  | None ->
      match Sys.getenv_opt "GILLIAN_SMT_TERMINAL_PROBE" with
      | None -> Alcotest.run "Gillian" test_suites
      | Some mode -> terminal_solver_probe mode
