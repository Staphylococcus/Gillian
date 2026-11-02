(* Observational only: no engine types, evaluation, solver calls or proof counters. *)
type context = { root : int; scope : int; parent_scope : int option; entry_state : int }
type session = {
  sink : string -> unit; max_bytes : int; max_events : int; max_event : int;
  mutable bytes : int; mutable events : int; mutable next : int;
  mutable unavailable : bool; mutable terminal : bool;
  mutable context : context option;
  mutable objects : (Obj.t Weak.t * int) list;
}
let requested = Sys.getenv_opt "GILLIAN_OWNED_PREFIX_LIFECYCLE_DIR"
let current : session option ref = ref None
let runtime : session option ref = ref None
let override : session option option ref = ref None
let active () = match !current with Some s -> not s.unavailable | None -> false
let focused = function
  | "S05StringCells" | "S05CompactOwnedPrefix" -> true | _ -> false
let fresh s = s.next <- s.next + 1; s.next
let output s text =
  s.sink text; s.bytes <- s.bytes + String.length text; s.events <- s.events + 1
let unavailable s reason =
  s.unavailable <- true;
  if not s.terminal then (
    s.terminal <- true;
    try
      let text = Yojson.Safe.to_string (`Assoc ["event",`String "unavailable";
        "reason",`String reason; "complete",`Bool false]) ^ "\n" in
      if s.events < s.max_events && s.bytes + String.length text <= s.max_bytes
      then output s text
    with _ -> ())
let make ?(bytes=262144) ?(events=512) ?(event_bytes=8192) sink =
  {sink; max_bytes=max 0 (min 262144 bytes); max_events=max 0 (min 512 events);
   max_event=max 0 (min 8192 event_bytes);
   bytes=0; events=0; next=0; unavailable=false; terminal=false;
   context=None; objects=[]}
let object_id s value =
  let value = Obj.repr value in
  s.objects <- List.filter (fun (key,_) -> Weak.check key 0) s.objects;
  match List.find_opt (fun (key,_) -> match Weak.get key 0 with
      | Some prior -> prior == value | None -> false) s.objects with
  | Some (_,id) -> id
  | None ->
      if List.length s.objects >= 512 then (unavailable s "state-id-cap"; 0)
      else let id = fresh s and key = Weak.create 1 in
        Weak.set key 0 (Some value); s.objects <- (key,id)::s.objects; id
let record s event state payload =
  if not s.unavailable then try
    match s.context with
    | None -> unavailable s "missing-root-or-scope"
    | Some c ->
        let data = payload () in
        let value = `Assoc ["format",`String "owned-prefix-lifecycle-v1";
          "id",`Int (fresh s); "root",`Int c.root; "scope",`Int c.scope;
          "parent_scope",(match c.parent_scope with None -> `Null | Some id -> `Int id);
          "scope_entry_state",`Int c.entry_state; "state",`Int state;
          "event",`String event; "complete",`Bool true; "proof_credit",`Bool false; "data",data] in
        let text = Yojson.Safe.to_string value ^ "\n" in
        if String.length text > s.max_event then unavailable s "event-byte-cap"
        else if s.events + 1 >= s.max_events || s.bytes + String.length text + 256 > s.max_bytes
        then unavailable s "capture-cap" else output s text
  with _ -> unavailable s "snapshot-or-serialization-or-io"
let event name ~state payload =
  match !current with
  | None -> ()
  | Some s when s.unavailable -> ()
  | Some s -> (try record s name (object_id s state) payload
      with _ -> unavailable s "state-snapshot")
let scope name ~state payload f =
  match !current with
  | None -> f ()
  | Some s when s.unavailable -> f ()
  | Some s ->
      let previous = s.context in
      (try match previous with
       | None -> unavailable s "missing-root"
       | Some parent ->
           let id = fresh s and entry_state = object_id s state in
           if entry_state = 0 then unavailable s "missing-branch-state";
           s.context <- Some {root=parent.root;scope=id;parent_scope=Some parent.scope;entry_state};
           record s (name ^ "-enter") entry_state payload
       with _ -> unavailable s "scope-snapshot");
      let returned = ref false in
      Fun.protect ~finally:(fun () ->
        event (name ^ "-exit") ~state (fun () -> `Assoc ["returned",`Bool !returned]);
        s.context <- previous) (fun () -> let value=f () in returned:=true; value)
let scope_if observe name ~state payload f =
  if observe then scope name ~state payload f else f ()
let runtime_session () =
  match !override with
  | Some value -> value
  | None -> match requested with
    | None -> None
    | Some directory -> (
        match !runtime with Some s -> Some s | None ->
        try
          if Filename.is_relative directory ||
             (Unix.lstat directory).Unix.st_kind <> Unix.S_DIR
          then invalid_arg "lifecycle capture needs a fresh absolute directory";
          let path = Filename.concat directory "owned-prefix-lifecycle.jsonl" in
          let fd = Unix.openfile path [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_EXCL] 0o600 in
          let channel = try Unix.out_channel_of_descr fd with exn -> Unix.close fd; raise exn in
          let s = make (fun text -> output_string channel text; flush channel) in
          at_exit (fun () -> close_out_noerr channel); runtime := Some s; Some s
        with _ ->
          let s = make (fun _ -> ()) in s.unavailable <- true;
          runtime := Some s; Some s)
let with_root ~target ~case_id ~state f =
  if target <> "S05CompactAppendOwned" then f () else
  match runtime_session () with
  | None -> f ()
  | Some s ->
      let previous = !current and prior_context = s.context in
      current := Some s;
      (try let root = fresh s and entry_state = object_id s state in
         if entry_state = 0 then unavailable s "missing-root-state";
         s.context <- Some {root;scope=root;parent_scope=None;entry_state};
         record s "root-enter" entry_state (fun () ->
           let a,b = case_id in `Assoc ["target",`String target;
             "case",`List [`Int a;`Int b]])
       with _ -> unavailable s "root-snapshot");
      let returned = ref false in
      Fun.protect ~finally:(fun () ->
        event "root-exit" ~state (fun () -> `Assoc ["returned",`Bool !returned]);
        s.context <- prior_context; current := previous)
        (fun () -> let value=f () in returned:=true; value)
let query ~query ~caller =
  match !current with
  | None -> ()
  | Some s -> (
      match s.context with
      | None -> unavailable s "missing-query-scope"
      | Some c when c.entry_state = 0 || query = "none" || query = "" ->
          unavailable s "missing-query-id-or-state"
      | Some c -> record s "native-query" c.entry_state (fun () ->
          `Assoc ["query",`String query;"caller",`String caller]))
module For_tests = struct
  let run ?(enabled=true) ?bytes ?events ?event_bytes sink f =
    let previous = !override in
    let s = make ?bytes ?events ?event_bytes sink in
    override := Some (if enabled then Some s else None);
    Fun.protect ~finally:(fun () -> override := previous) (fun () ->
      let result = f () in result, not s.unavailable)
end
