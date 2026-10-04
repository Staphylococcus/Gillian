(** Opt-in, source-bound Babel phase. The profile and transformer are part of
    the trusted compiler boundary; this is not a proof of Babel itself. *)
exception Frontend_error of string

let profile = ref None
let fail message = raise (Frontend_error message)

let string json key =
  match Yojson.Safe.Util.member key json with
  | `String value -> value
  | _ -> fail ("ES2015 frontend profile requires string " ^ key)

let pin json =
  let path = string json "path" in
  let expected = string json "sha256" in
  let channel =
    Unix.open_process_args_in "/usr/bin/sha256sum"
      [| "/usr/bin/sha256sum"; "--"; path |]
  in
  let line = try input_line channel with End_of_file -> "" in
  let status = Unix.close_process_in channel in
  let actual = if String.length line >= 64 then String.sub line 0 64 else "" in
  if status <> Unix.WEXITED 0 || actual <> expected then
    fail ("ES2015 frontend executable pin mismatch: " ^ path);
  path

let transform ~path source =
  match !profile with
  | None -> source
  | Some profile_path -> (
      try
        (* S01 compiles the exact stored source. Do not silently combine this
           phase with synthetic harness/strict/cosette source rewriting. *)
        if source <> Javert_utils.Io_utils.load_file path then
          fail "ES2015 frontend requires exact stored source; injected source is unsupported";
        let json = Yojson.Safe.from_file profile_path in
        let node = pin (Yojson.Safe.Util.member "node" json) in
        let bridge = pin (Yojson.Safe.Util.member "bridge" json) in
        let channel =
          Unix.open_process_args_in node
            [| node; bridge; profile_path; path |]
        in
        let result = Buffer.create (String.length source) in
        (try
           while true do
             Buffer.add_string result (input_line channel);
             Buffer.add_char result '\n'
           done
         with End_of_file -> ());
        match Unix.close_process_in channel with
        | Unix.WEXITED 0 -> Buffer.contents result
        | _ -> fail "Pinned ES2015 frontend rejected source; no proof was attempted"
      with
      | Frontend_error _ as error -> raise error
      | error -> fail ("ES2015 frontend failed: " ^ Printexc.to_string error))
