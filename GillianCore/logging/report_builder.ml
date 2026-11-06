module Report_state = struct
  (* Serialized content stays immutable when the original loggable contains
     mutable state. Snapshots belong to this state, never an ID-indexed cache. *)
  type snapshot = Report_id.t * string * string
  type t = {
    previous : Report_id.t option ref;
    parents : (Report_id.t * snapshot option) Stack.t;
    pending_snapshot : snapshot option ref;
  }

  let make () = {
    previous = ref None; parents = Stack.create (); pending_snapshot = ref None;
  }

  let clone { previous; parents; pending_snapshot } = {
    previous = ref !previous; parents = Stack.copy parents;
    pending_snapshot = ref !pending_snapshot;
  }

  let global_state = make ()
  let active_state = ref global_state
  let activate state = active_state := state

  let with_state f state =
    let prev_report_state = !active_state in
    active_state := state;
    let result = f () in
    active_state := prev_report_state;
    result
end

open Report_state

let get_previous () =
  let { previous; _ } = !active_state in
  !previous

let set_previous ?(force_none = false) id =
  let { previous; _ } = !active_state in
  match id with
  | None when not force_none -> ()
  | _ -> previous := id

let get_parent () =
  let { parents; _ } = !active_state in
  Option.map fst (Stack.top_opt parents)

let get_parent_snapshot () =
  let { parents; _ } = !active_state in
  match Stack.top_opt parents with
  | Some (id, Some ((snapshot_id, type_, _) as snapshot))
    when Report_id.equal id snapshot_id
         && type_ = Logging_constants.Content_type.cmd -> Some snapshot
  | _ -> None

let set_parent id =
  let { previous; parents; pending_snapshot } = !active_state in
  let snapshot = match !pending_snapshot with
    | Some ((pending_id, _, _) as snapshot) when Report_id.equal id pending_id ->
        Some snapshot
    | _ -> None
  in
  pending_snapshot := None;
  previous := None;
  Stack.push (id, snapshot) parents

let release_parent = function
  | None -> ()
  | Some rid as id_opt ->
      let { previous; parents; pending_snapshot } = !active_state in
      let parent_id, _ = Stack.pop parents in
      assert (Report_id.equal rid parent_id);
      pending_snapshot := None;
      previous := id_opt

(* Bound the encoded envelope including content_json escaping. Observer errors
   make a snapshot unavailable; they cannot become proof/execution errors. *)
let capture_parent_snapshot (report : Report.t) =
  try
    if report.type_ <> Logging_constants.Content_type.cmd
       || Sys.getenv_opt "GILLIAN_NATIVE_SMT_CONTEXT_DIR" = None
       || Sys.getenv_opt "GILLIAN_NATIVE_SMT_CONTEXT_SCOPES_ONLY" = Some "1" then None
    else
      let content = Yojson.Safe.to_string
        (Loggable.loggable_to_yojson report.content) in
      let encoded = Yojson.Safe.to_string (`Assoc [
        ("id", Report_id.to_yojson report.id);
        ("type", `String report.type_); ("content_json", `String content) ]) in
      if String.length encoded > 8 * 1024 * 1024 then None
      else Some (report.id, report.type_, content)
  with _ -> None

let make
    ?title
    ~(content : Loggable.t)
    ~(type_ : string)
    ?(severity = Logging_constants.Severity.Log)
    () =
  let title =
    match title with
    | None -> type_
    | Some title -> title
  in
  let report : Report.t =
    {
      id = Report_id.next ();
      title;
      elapsed_time = Unix.gettimeofday ();
      previous = get_previous ();
      parent = get_parent ();
      content;
      severity;
      type_;
    }
  in
  let { pending_snapshot; _ } = !active_state in
  pending_snapshot := capture_parent_snapshot report;
  set_previous (Some report.id);
  report

let start_phase level ?title ?severity () =
  if Mode.should_log level then (
    let report =
      make ?title
        ~content:(Loggable.make_string "*** Phase ***")
        ~type_:Logging_constants.Content_type.phase ?severity ()
    in
    set_parent report.id;
    Some report)
  else None

let end_phase = release_parent
