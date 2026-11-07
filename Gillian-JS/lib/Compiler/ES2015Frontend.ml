(** Opt-in, source-bound Babel phase. The profile and transformer are part of
    the trusted compiler boundary; this is not a proof of Babel itself. *)
exception Frontend_error of string

let profile = ref None
let fail message = raise (Frontend_error message)
let parameter_origins = ref []
let reset_origins () = parameter_origins := []

let unmapped_arguments fid params =
  match !profile, List.assoc_opt fid !parameter_origins with
  | Some _, Some (expected, used) ->
      if params <> expected then fail "Unmapped argument origin has different lowered parameters";
      if !used then fail "Unmapped argument origin was consumed more than once";
      used := true;
      true
  | _ -> false

let finish_origins () =
  if List.exists (fun (_, (_, used)) -> not !used) !parameter_origins then
    fail "Unmapped argument origin did not match an eligible function"

let string json key =
  match Yojson.Safe.Util.member key json with
  | `String value -> value
  | _ -> fail ("ES2015 frontend profile requires string " ^ key)

let decode_parameter_origins expected_hash output =
  reset_origins ();
  try
  let json = Yojson.Safe.from_string output in
  if string json "sourceSHA256" <> expected_hash then
    fail "Unmapped argument origins refer to a different source unit";
  let source = string json "source" in
  let origins = match Yojson.Safe.Util.member "unmappedArguments" json with
    | `List rows -> List.map (fun row ->
        let id = string row "id" in
        if id = "" || String.exists (fun c ->
            not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                 (c >= '0' && c <= '9') || c = '_')) id then
          fail "Invalid unmapped argument function identity";
        if Yojson.Safe.Util.member "nonSimpleParameters" row <> `Bool true ||
           Yojson.Safe.Util.member "implicitArguments" row <> `Bool true ||
           Yojson.Safe.Util.member "originalStrict" row <> `Bool false then
          fail "Unmapped arguments require an implicit non-simple non-strict origin";
        let params = match Yojson.Safe.Util.member "loweredParameters" row with
          | `List values -> List.map (function `String p when p <> "arguments" -> p
              | _ -> fail "Invalid unmapped argument lowered parameters") values
          | _ -> fail "Unmapped argument origin requires lowered parameters" in
        id, (params, ref false)) rows
    | _ -> fail "Frontend envelope requires unmapped argument origins" in
  let ids = List.map fst origins in
  if List.length (List.sort_uniq String.compare ids) <> List.length ids then
    fail "Duplicate unmapped argument function identity";
  parameter_origins := origins;
  source
  with Yojson.Json_error _ -> fail "Malformed parameter-origin envelope"

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
  reset_origins ();
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
        | Unix.WEXITED 0 ->
            (match Yojson.Safe.Util.member "outputProtocol" json with
             | `Null -> Buffer.contents result
             | `String "source-and-parameter-origins-v1" ->
                 decode_parameter_origins
                   (string (Yojson.Safe.Util.member "source" json) "sha256")
                   (Buffer.contents result)
             | _ -> fail "Unknown ES2015 frontend output protocol")
        | _ -> fail "Pinned ES2015 frontend rejected source; no proof was attempted"
      with
      | Frontend_error _ as error -> raise error
      | error -> fail ("ES2015 frontend failed: " ^ Printexc.to_string error))
