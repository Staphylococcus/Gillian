(* Passive, explicitly opted-in diagnostics. This module owns no proof state. *)
type body = { target : string; case_id : int * int }
type capture = {
  directory : string;
  target : string;
  mutable active : body option;
  mutable disabled : bool;
  mutable busy : bool;
  mutable files : int;
  mutable bytes : int;
  mutable snapshots : int;
}

let max_file_bytes = 64 * 1024
let max_total_bytes = 1024 * 1024
let max_files = 16
let max_snapshots = 2
let capture : capture option ref = ref None

let disable c = c.disabled <- true

let metadata body phase =
  let public_id, normalized_id = body.case_id in
  Printf.sprintf
    "pid=%d\ntarget=%s\npublic_case=%d\nnormalized_case=%d\nphase=%s\ntime=%.6f\n"
    (Unix.getpid ()) (String.escaped body.target) public_id normalized_id
    phase (Unix.gettimeofday ())

let emit c text =
  if not c.disabled then
    try
      let text = if String.length text > max_file_bytes then
          String.sub text 0 max_file_bytes else text in
      if c.files >= max_files || c.bytes + String.length text > max_total_bytes
      then disable c
      else (
        let file = Filename.concat c.directory
            (Printf.sprintf "verify-body-%d-%06d.log" (Unix.getpid ()) (c.files + 1)) in
        (* Charge before IO; errors disable capture, never trigger a retry. *)
        c.files <- c.files + 1;
        c.bytes <- c.bytes + String.length text;
        let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL ] 0o600 in
        Fun.protect ~finally:(fun () -> Unix.close fd) (fun () ->
            let rec write offset =
              if offset < String.length text then
                let count = Unix.write_substring fd text offset (String.length text - offset) in
                if count = 0 then failwith "diagnostic write made no progress"
                else write (offset + count)
            in
            write 0))
    with _ -> disable c

let event c body phase =
  try emit c (metadata body phase) with _ -> disable c

let signal_snapshot _ =
  match !capture with
  | Some c when not c.disabled && not c.busy && c.snapshots < max_snapshots ->
      (match c.active with
      | None -> ()
      | Some body ->
          c.busy <- true;
          (try
             c.snapshots <- c.snapshots + 1;
             let stack = Printexc.get_callstack 128 |> Printexc.raw_backtrace_to_string in
             emit c (metadata body "BODY_STACK" ^ "stack_frames_limit=128\n" ^ stack)
           with _ -> disable c);
          c.busy <- false)
  | _ -> ()

let () =
  try
    match Sys.getenv_opt "GILLIAN_VERIFY_BODY_STACK_DIR",
          Sys.getenv_opt "GILLIAN_VERIFY_BODY_STACK_TARGET" with
    | None, None -> ()
    | directory, target ->
        (* Keep the no-op handler installed even after BODY/capture ends or
           configuration fails: a late diagnostic signal must not terminate
           verification. With no opt-in environment, signals are untouched. *)
        Sys.set_signal Sys.sigusr1 (Sys.Signal_handle signal_snapshot);
        (match directory, target with
        | Some directory, Some target
          when directory <> "" && target <> "" && String.length target <= 256 &&
               not (Filename.is_relative directory) ->
            let info =
              try Unix.lstat directory with
              | Unix.Unix_error (Unix.ENOENT, _, _) ->
                  Unix.mkdir directory 0o700;
                  Unix.lstat directory in
            if info.Unix.st_kind = Unix.S_DIR &&
               info.st_uid = Unix.geteuid () && info.st_perm land 0o077 = 0 then
              capture := Some { directory; target; active = None; disabled = false;
                                busy = false; files = 0; bytes = 0; snapshots = 0 }
        | _ -> ())
  with _ -> ()

let with_body ~target ~case_id action =
  match !capture with
  | Some c when not c.disabled && c.target = target ->
      let start =
        try
          let body = { target; case_id } in
          event c body "BODY_ENTER";
          if c.disabled then None else Some (body, c.active, Some body)
        with _ -> disable c; None in
      (match start with
      | None -> action ()
      | Some (body, previous, active) ->
          c.active <- active;
          match action () with
          | result ->
              c.active <- previous;
              event c body "BODY_RETURN";
              result
          | exception exn ->
              let backtrace = Printexc.get_raw_backtrace () in
              c.active <- previous;
              event c body "BODY_EXCEPTION";
              Printexc.raise_with_backtrace exn backtrace)
  | _ -> action ()
