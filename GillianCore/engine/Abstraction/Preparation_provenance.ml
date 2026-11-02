(* Passive preparation provenance. No proof facts, normalization or solver calls. *)
open Containers
module C = Linked_program_capture.Codec
module F = Preparation_framing
module Snapshot = Preparation_snapshot

let max_bytes = 16 * 1024 * 1024
let max_events = 4096
let max_record = 1024 * 1024
let max_carriers = 4096
let terminal_reserve = 4096

(* Keep this policy identical to the former Verifier selector. *)
let select_procs_and_lemmas ~procs_to_verify ~lemmas_to_verify =
  let module C = Config.Verification in
  let ps, ls =
    match !C.things_to_verify with
    | All -> (procs_to_verify, lemmas_to_verify)
    | ProcsOnly -> (procs_to_verify, SS.empty)
    | LemmasOnly -> (SS.empty, lemmas_to_verify)
    | Specific ->
        ( SS.inter procs_to_verify (SS.of_list !C.procs_to_verify),
          SS.inter lemmas_to_verify (SS.of_list !C.lemmas_to_verify) )
  in
  let ps = SS.diff ps !C.things_to_exclude in
  let ls = SS.diff ls !C.things_to_exclude in
  (ps, ls)

type source = {
  kind : string; name : string; groups : bool array;
  mutable expanded : int;
}
type origin = {
  source : source; raw_parent : int; alternative : int; expanded : int;
  carrier : Obj.t; mutable begun : bool;
  mutable to_verify : bool option;
  mutable normalised : int option; mutable states : int; mutable tests : int;
}
type session = {
  path : string; identity : string; sink : string -> unit; close : unit -> unit;
  receipt : bool -> string -> unit;
  byte_cap : int; event_cap : int; record_cap : int; carrier_cap : int;
  mutable bytes : int; mutable events : int; mutable failed : string option;
  framed : bool; alternative : bool; snapshot : Snapshot.t option; mutable group_open : bool;
  mutable logical_events : int;
  mutable terminal : bool; mutable closed : bool;
  mutable sources : source list; mutable origins : origin list;
  mutable prepared_inputs : (source * int * Obj.t) list;
  mutable preparation_stage_started : bool; mutable preparation_stage_complete : bool;
  mutable procedures : SS.t; mutable lemmas : SS.t;
}
let current : session option ref = ref None
let enabled () = match !current with Some s -> not s.terminal | None -> false
let field_framed () = match !current with Some s -> Option.is_some s.snapshot | None -> false
(* V4-only private import index: this is the exact existing immutable source
   registry object, never native state/value identity. The registry is complete
   before expansion and unchanged through normalization/test construction. *)
let snapshot_source_index s wanted =
  let rec find i = function
    | []->raise(C.Incomplete "v4-source-not-in-current-registry")
    | source::rest->C.require(i<4096)"v4-source-registry-cap";
      if source==wanted then i else find(i+1)rest in
  find 0 s.sources
let require = C.require
(* Capture-local aggregate admission, not an AST/transport policy change.
   Inspect the admitted physical graph, counting repeated aliases, under the
   former default C.inspect resource bounds. Expanded-parent projects its opaque
   identity handles out below; the other three sites retain their whole graph.
   An explicit worklist avoids OCaml list-spine recursion/depth failure;
   the existing typed AST, state and transport guards still run before their
   serializers. Custom blocks are discovered here, never cast or converted. *)
type aggregate_stage = Posts | Expanded_parent | Original_procs | Original_lemmas
let inspect_aggregate stage value =
  let stage = match stage with
    | Posts -> "posts" | Expanded_parent -> "expanded-parent"
    | Original_procs -> "original-procs" | Original_lemmas -> "original-lemmas"
  in
  try
    let nodes = ref 0 and words = ref 0 and strings = ref 0 and customs = ref [] in
    let active = ref [] and work = ref [`Enter (Obj.repr value)] in
    while !work <> [] do
      match !work with
      | [] -> ()
      | `Leave raw :: rest ->
          work := rest;
          (match !active with
           | current :: tail when current == raw -> active := tail
           | _ -> raise (C.Incomplete "aggregate active path accounting"))
      | `Enter raw :: rest ->
          work := rest;
          incr nodes;
          require ((match !current with Some s -> s.framed | None -> false) ||
            !nodes <= 32768) "aggregate occurrence budget32768";
          if not (Obj.is_int raw) then (
            require (not (List.exists (fun prior -> prior == raw) !active))
              "cyclic capture fragment";
            let tag = Obj.tag raw and size = Obj.size raw in
            words := !words + size + 1;
            require (!words <= 262144) "value word budget";
            if tag = Obj.string_tag then (
              let n = String.length (Obj.obj raw : string) in
              strings := !strings + n;
              require (n <= 65536 && !strings <= 262144) "value string budget")
            else if tag = Obj.double_tag || tag = Obj.double_array_tag then ()
            else if tag = Obj.custom_tag then customs := raw :: !customs
            else (
              require (tag < Obj.lazy_tag) "unsupported host shape/closure";
              active := raw :: !active;
              work := `Leave raw :: !work;
              for i = size - 1 downto 0 do
                work := `Enter (Obj.field raw i) :: !work
              done))
    done;
    !customs
  with C.Incomplete why ->
    raise (C.Incomplete ("aggregate:" ^ stage ^ ": " ^ why))
(* Bound aggregate integer conversion work, including repeated shared values.
   Existing occurrence/word/string guards do not account for Zarith limbs. *)
let integer_bits = ref None
let charge_integer bits =
  require (bits <= 65536) "integer-bit-cap";
  match !integer_bits with
  | None -> ()
  | Some used -> used := !used + max 1 bits;
      require (!used <= 1048576) "record-integer-conversion-cap"
let typed_guard visit value =
  C.guard_ast_v3 visit value;
  let used = ref 0 in
  let visitor = object
    inherit [_] Visitors.iter as super
    method! visit_literal env literal = match literal with
      | Literal.Int z ->
          let bits = Z.numbits z in
          used := !used + max 1 bits;
          require (!used <= 1048576) "typed-integer-conversion-cap";
          charge_integer bits
      | _ -> super#visit_literal env literal
  end in
  visit visitor value
let close s =
  if not s.closed then (s.closed <- true;
    Fun.protect ~finally:(fun()->Option.iter Snapshot.release s.snapshot) s.close)
let envelope s event complete fields = `Assoc
  (["format", `String (if Option.is_some s.snapshot then "gillian-preparation-provenance-field-framed-v4"
       else if s.alternative then "gillian-preparation-provenance-alternative-framed-v3"
       else if s.framed then "gillian-preparation-provenance-framed-v2"
       else "gillian-preparation-provenance-v1");
    "encoding", `String "linked-capture-lossless-v1";
    "session", `String s.identity; "sequence", `Int s.events;
    "event", `String event; "complete", `Bool complete;
    "proof_credit", `Bool false] @ fields)
let output s text =
  (* Charge before IO; partial writes can never be retried as a fresh event. *)
  s.bytes <- s.bytes + String.length text; s.events <- s.events + 1;
  s.sink text
let fail s event reason =
  if not s.terminal then (
    s.failed <- Some reason; s.terminal <- true;
    (try
       let text = Yojson.Safe.to_string (envelope s event false
         ["reason", `String reason]) ^ "\n" in
       if s.events < s.event_cap && s.bytes + String.length text <= s.byte_cap
       then output s text
     with _ -> ());
    (try close s with _ -> ());
    (try s.receipt false reason with _ -> ()))
let observe f = match !current with
  | None -> ()
  | Some s when s.terminal -> ()
  | Some s ->
      (try f s with
       | C.Incomplete why -> fail s "overflow" why
       | _ -> fail s "error" "snapshot-serialization-or-io")
let emit_v1 s event fields =
  require (not s.terminal) "terminal capture";
  let previous = !integer_bits in
  let payload = Fun.protect ~finally:(fun () -> integer_bits := previous)
    (fun () -> integer_bits := Some (ref 0); fields ()) in
  C.guard_transport payload;
  let tagged = C.tag payload in
  C.guard_transport tagged;
  let text = Yojson.Safe.to_string (envelope s event false
    ["data", tagged]) ^ "\n" in
  require (String.length text <= s.record_cap) "record-byte-cap";
  require (s.events + 1 < s.event_cap &&
    s.bytes + String.length text + terminal_reserve <= s.byte_cap)
    "total-byte-or-event-cap";
  output s text
(* Frames and commits are physical records; the framed bytes contain the exact
   v1 logical envelope with an independent logical sequence. One event in flight.
   The old whole-event occurrence/depth gates are intentionally not reapplied. *)
let physical s event fields =
  let row=envelope s event false fields in
  ignore(C.inspect ~node_limit:32768 ~word_limit:262144 row);
  let text=Yojson.Safe.to_string row ^ "\n" in
  require (String.length text <= s.record_cap) "record-byte-cap";
  require (s.events + 1 < s.event_cap &&
    s.bytes + String.length text + terminal_reserve <= s.byte_cap)
    "total-byte-or-event-cap";
  output s text
let emit_framed ?body s event stream =
  require (not s.terminal) "terminal capture";
  require (Sys.word_size = 64 && String.length s.identity <= 4096 && String.length event <= 128 &&
    String.for_all(fun c -> Char.code c<128)s.identity &&
    String.for_all(fun c -> Char.code c<128)event)
    "v2-bounded-envelope";
  let index=ref 0 and offset=ref 0 and digest=ref F.checksum_initial in
  let buffer=Buffer.create F.chunk_bytes in
  let flush () = if Buffer.length buffer>0 then (
    let chunk=Buffer.contents buffer in
    require (String.for_all(fun c -> Char.code c<128)chunk) "v2-ascii-logical-bytes";
    physical s "frame" ["logical_sequence",`Int s.logical_events;
      "index",`Int !index;"offset",`Int !offset;"length",`Int(String.length chunk);
      "chunk_encoding",`String "ascii-json-string";
      "checksum_kind",`String "fnv1a64-transport-only";
      "checksum",`String(F.checksum_text chunk);"bytes",`String chunk];
    digest:=F.checksum_update !digest chunk;
    incr index;offset:= !offset+String.length chunk;Buffer.clear buffer) in
  let put text =
    let rec copy at = if at<String.length text then (
      let n=min (F.chunk_bytes-Buffer.length buffer) (String.length text-at) in
      require (!offset + Buffer.length buffer + n <= max_bytes)
        "logical-event-byte-cap";
      Option.iter(fun d -> Snapshot.append d (String.sub text at n))s.snapshot;
      Buffer.add_substring buffer text at n;
      if Buffer.length buffer=F.chunk_bytes then flush ();
      copy (at+n)) in copy 0 in
  let previous= !integer_bits in
  Fun.protect ~finally:(fun () -> integer_bits:=previous) (fun () ->
    integer_bits:=Some(ref 0);
    (match body with Some write -> write put | None ->
    let prefix=Yojson.Safe.to_string (`Assoc [
      "format",`String (if Option.is_some s.snapshot then
        "gillian-preparation-provenance-fields-v4" else if s.alternative then
        "gillian-preparation-provenance-alternatives-v3" else "gillian-preparation-provenance-v1");
      "encoding",`String "linked-capture-lossless-v1";
      "session",`String s.identity;"sequence",`Int s.logical_events;
      "event",`String event;"complete",`Bool false;"proof_credit",`Bool false]) in
    put (String.sub prefix 0 (String.length prefix-1));put ",\"data\":";
    stream (F.create put);put "}\n");flush ());
  physical s "commit" ["logical_sequence",`Int s.logical_events;
    "frames",`Int !index;"length",`Int !offset;
    "checksum_kind",`String "fnv1a64-transport-only";
    "checksum",`String(F.checksum !digest)];
  Option.iter(fun d -> Snapshot.commit d ~sequence:s.logical_events)s.snapshot;
  s.logical_events<-s.logical_events+1
let emit s event fields =
  if s.framed then emit_framed s event (fun t -> F.json (fields ()) t)
  else emit_v1 s event fields
let emit_choice s event old stream =
  if s.framed then emit_framed s event stream else emit_v1 s event old
let ast a =
  typed_guard (fun v x -> v#visit_assertion () x) a;
  Asrt.to_yojson a
let expr e =
  typed_guard (fun v x -> v#visit_expr () x) e;
  Expr.to_yojson e
let located (a, loc) =
  `Assoc ["assertion", ast a; "location", (match loc with
    | None -> `Null | Some l -> C.guard_plain l; Location.to_yojson l)]
let posts ps =
  ignore (inspect_aggregate Posts ps);
  `List (List.map located ps)
let optional_expr = function None -> `Null | Some e -> expr e
let source_fields source =
  ["kind", `String source.kind; "name", `String source.name]
let origin_fields o = source_fields o.source @
  ["raw_parent", `Int o.raw_parent; "alternative", `Int o.alternative;
   "expanded", `Int o.expanded]
(* Outer event builders stream one already guarded derived leaf at a time. *)
let stream_leaf convert t = F.json (convert ()) t
let stream_ast a = stream_leaf (fun () -> ast a)
let stream_expr e = stream_leaf (fun () -> expr e)
let stream_location = function
  | None -> F.null
  | Some l -> stream_leaf (fun () -> C.guard_plain l;Location.to_yojson l)
let stream_located (a,loc) = F.fields ["assertion",stream_ast a;
  "location",stream_location loc]
let stream_posts ps t =
  ignore(inspect_aggregate Posts ps);
  F.list (fun add -> List.iter (fun p -> add(stream_located p)) ps) t
let stream_optional_expr = function None -> F.null | Some e -> stream_expr e
let stream_source source = ["kind",F.bytes source.kind;"name",F.bytes source.name]
let stream_origin o = stream_source o.source @
  ["raw_parent",F.int o.raw_parent;"alternative",F.int o.alternative;
   "expanded",F.int o.expanded]
let selected s kind name = SS.mem name
  (if kind = "procedure" then s.procedures else s.lemmas)
let captures kind name = match !current with
  | Some s when not s.terminal -> selected s kind name
  | _ -> false
let find_source s kind name =
  List.find_opt (fun x -> x.kind = kind && x.name = name) s.sources
let add_source s kind name count =
  require (count >= 0 && count <= s.carrier_cap) "raw-parent-cap";
  require (List.length s.sources < s.carrier_cap &&
    List.fold_left (fun n x -> n + Array.length x.groups) count s.sources
      <= s.carrier_cap) "source-registry-cap";
  require (find_source s kind name = None) "duplicate-source-name";
  let source = {kind; name; groups = Array.make count false; expanded = 0} in
  s.sources <- source :: s.sources; source
let register_group kind name raw_parent input outputs = observe (fun s ->
  if selected s kind name then (
    require (not s.alternative) "v3-requires-projected-alternatives";
    let source = match find_source s kind name with
      | Some x -> x | None -> raise (C.Incomplete "missing-original-source") in
    require (raw_parent >= 0 && raw_parent < Array.length source.groups &&
      not source.groups.(raw_parent)) "duplicate-or-out-of-range-parent";
    let rec count_outputs remaining count = function
      | [] -> count
      | _ :: rest ->
          require (remaining > 0) "expanded-carrier-cap";
          count_outputs (remaining - 1) (count + 1) rest
    in
    let output_count =
      count_outputs (s.carrier_cap - List.length s.origins) 0 outputs in
    (* The carrier is only an opaque physical origin handle. Meter the complete
       emitted source/assertion projection once, including input_pre and each
       actual repeated PRE/POST occurrence, under one unchanged aggregate budget.
       Bound the output/remaining-origin count before allocating the projection. *)
    ignore (inspect_aggregate Expanded_parent
      (input, List.map (fun (_, pre, post) -> pre, post) outputs));
    let first = source.expanded in
    if s.framed then (
      (* Publish identity registry entries only after complete event commit. *)
      let staged=ref [] in
      let origins=List.mapi(fun alternative (carrier,pre,post) ->
        let carrier=Obj.repr carrier in
        require (not(List.exists(fun o -> o.carrier==carrier) (s.origins @ !staged)))
          "ambiguous-physical-carrier";
        let o={source;raw_parent;alternative;expanded=first+alternative;
          carrier;begun=false;to_verify=None;normalised=None;states=0;tests=0} in
        staged:=o:: !staged;o,pre,post) outputs in
      emit_framed s "expanded-parent" (F.fields (stream_source source @
        ["raw_parent",F.int raw_parent;"input_pre",stream_located input;
         "first_expanded",F.int first;"output_count",F.int output_count;
         "outputs",F.list(fun add -> List.iter(fun (o,pre,post) ->
           add(F.fields(stream_origin o @ ["pre",stream_located pre;
             "posts",stream_posts post]))) origins)]));
      s.origins<- !staged @ s.origins)
    else (
    emit_v1 s "expanded-parent" (fun () ->
    let mapped = List.mapi (fun alternative (carrier, pre, post) ->
      let carrier = Obj.repr carrier in
      require (not (List.exists (fun o -> o.carrier == carrier) s.origins))
        "ambiguous-physical-carrier";
      let o = {source; raw_parent; alternative; expanded = first + alternative;
        carrier; begun = false; to_verify = None;
        normalised = None; states = 0; tests = 0} in
      s.origins <- o :: s.origins;
      `Assoc (origin_fields o @ ["pre", located pre; "posts", posts post])) outputs in
    `Assoc (source_fields source @
      ["raw_parent", `Int raw_parent; "input_pre", located input;
       "first_expanded", `Int first; "output_count", `Int output_count;
       "outputs", `List mapped])));
    source.groups.(raw_parent) <- true;
    source.expanded <- first + output_count))
(* V3 deliberately changes admission from a whole expanded parent to its
   input and each complete (PRE, POST-list) alternative. The typed projector
   reads the existing carrier list directly: no projection map or giant parent
   JSON/tree is constructed. The preliminary count is bounded before staging.
   A physical carrier remains identity-only and every alias occurrence in PRE
   and POSTs is charged/serialized. Origins become visible only after end commit. *)
let all_groups_closed s = (not s.alternative || s.preparation_stage_complete) &&
  not s.group_open && List.for_all (fun source ->
  Array.for_all Fun.id source.groups) s.sources
let v3_context phase kind name parent alternative f =
  try f () with C.Incomplete why ->
    (* Names are bounded hex prefixes; all other fields are known scalars. No
       failed value is traversed again and the diagnostic fits terminal reserve. *)
    let name = String.sub name 0 (min 64 (String.length name)) in
    let hex = C.hex name in
    raise (C.Incomplete (Printf.sprintf
      "v3:%s:%s:name_hex=%s:parent=%d:alternative=%d: %s"
      phase kind hex parent alternative why))
let register_projected_group kind name raw_parent input outputs project =
  observe (fun s -> if selected s kind name then (
    let source = match find_source s kind name with
      | Some x -> x | None -> raise (C.Incomplete "missing-original-source") in
    v3_context "group" kind name raw_parent (-1) (fun () ->
    require (s.alternative && s.preparation_stage_complete)
      "expanded-parent-before-pre-expansion-stage";
    require (not s.group_open) "nested-expanded-parent";
    require (raw_parent >= 0 && raw_parent < Array.length source.groups &&
      not source.groups.(raw_parent)) "duplicate-or-out-of-range-parent";
    let rec count remaining n = function
      | [] -> n
      | _ :: rest -> require (remaining > 0) "expanded-carrier-cap";
          count (remaining - 1) (n + 1) rest in
    let output_count = count (s.carrier_cap - List.length s.origins) 0 outputs in
    require (List.exists (fun (prior,ordinal,known) -> prior == source &&
      ordinal=raw_parent && known == Obj.repr input) s.prepared_inputs)
      "expansion-input-not-prepared-parent";
    let first = source.expanded and staged = ref [] in
    s.group_open <- true;
    v3_context "begin-input" kind name raw_parent (-1) (fun () ->
      ignore (inspect_aggregate Expanded_parent input);
      emit_framed s "expanded-parent-begin" (F.fields (stream_source source @
        ["raw_parent",F.int raw_parent;"input_pre",stream_located input;
         "first_expanded",F.int first;"output_count",F.int output_count])));
    List.iteri (fun alternative carrier ->
      v3_context "alternative" kind name raw_parent alternative (fun () ->
        let pre,post = project carrier in
        ignore (inspect_aggregate Expanded_parent (pre,post));
        let raw = Obj.repr carrier in
        require (not (List.exists (fun o -> o.carrier == raw) s.origins) &&
          not (List.exists (fun o -> o.carrier == raw) !staged))
          "ambiguous-physical-carrier";
        let o = {source;raw_parent;alternative;expanded=first+alternative;
          carrier=raw;begun=false;to_verify=None;normalised=None;states=0;tests=0} in
        let import role convert t = match s.snapshot with
        | None -> F.json (convert ()) t
        | Some d ->
          let value=convert()and sequence=s.logical_events in
          let offset=Snapshot.position d in F.json value t;
          Snapshot.remember_import d ~sequence
            ~origin:(Snapshot.origin_key ~source:(snapshot_source_index s source) ~parent:raw_parent ~alternative
              ~expanded:o.expanded) ~role ~offset
            ~bytes:(Snapshot.position d-offset) value in
        (match s.snapshot with
        | None -> emit_framed s "expanded-alternative" (F.fields (stream_origin o @
          ["pre",stream_located pre;"posts",stream_posts post]))
        | Some _ -> emit_framed s "expanded-alternative" (F.fields(stream_origin o @
          ["pre",import "pre"(fun()->located pre);"posts",import "posts"(fun()->posts post)])));
        staged := o :: !staged)) outputs;
    v3_context "end" kind name raw_parent (-1) (fun () ->
      emit_framed s "expanded-parent-end" (F.fields (stream_source source @
        ["raw_parent",F.int raw_parent;"first_expanded",F.int first;
         "output_count",F.int output_count])));
    s.origins <- !staged @ s.origins;
    source.groups.(raw_parent) <- true; source.expanded <- first + output_count;
    s.group_open <- false)))
let spec_group name ordinal input outputs =
  observe (fun s -> if selected s "procedure" name then
  if s.alternative then register_projected_group "procedure" name ordinal input
    outputs (fun (c : Spec.st) -> c.ss_pre,c.ss_posts)
  else register_group "procedure" name ordinal input
    (List.map (fun (c : Spec.st) -> c, c.ss_pre, c.ss_posts) outputs))
let lemma_group name ordinal input outputs =
  observe (fun s -> if selected s "lemma" name then
  if s.alternative then register_projected_group "lemma" name ordinal input
    outputs (fun (c : Lemma.spec) -> c.lemma_hyp,c.lemma_concs)
  else register_group "lemma" name ordinal input
    (List.map (fun (c : Lemma.spec) -> c, c.lemma_hyp, c.lemma_concs) outputs))
let origin kind name carrier =
  let found = ref None in
  observe (fun s -> if selected s kind name then (
    require (not s.alternative || all_groups_closed s) "origin-before-group-closure";
    match List.find_opt (fun o -> o.carrier == Obj.repr carrier) s.origins with
    | Some o when o.source.kind = kind && o.source.name = name && not o.begun ->
        o.begun <- true; found := Some o
    | _ -> raise (C.Incomplete "missing-duplicate-or-mismatched-carrier")));
  !found
let with_origin_context s phase o f =
  if s.alternative then v3_context phase o.source.kind o.source.name
    o.raw_parent o.alternative f else f ()
let normalised origin ~to_verify get_count status = Option.iter (fun o -> observe (fun s ->
  with_origin_context s "normalization-complete" o (fun () ->
  require (not s.alternative || all_groups_closed s) "normalization-before-group-closure";
  let count = get_count () in
  require (o.normalised = None) "duplicate-normalization-completion";
  require (count >= 0 && count <= s.carrier_cap) "normalized-state-cap";
  let emit () = emit_choice s "normalization-complete"
    (fun () -> `Assoc (origin_fields o @ ["count",`Int count;"status",`String status]))
    (F.fields(stream_origin o @ ["count",F.int count;"status",F.bytes status])) in
  if s.framed then emit ();
  o.normalised <- Some count;
  o.to_verify <- Some to_verify;
  if not s.framed then emit ()))) origin

(* Public JSON omits pred_defs, which is a static program table. Inspect exactly
   the serialized state/preds/wands before invoking any derived serializer.
   The read-only assertion exporter supplies typed evidence for every custom
   block. Unknown or dropped serialized custom data is rejected, never cast. *)
let guarded_state ~projection ~assertions ~to_json =
  let customs = C.inspect ~node_limit:131072 ~word_limit:1048576
      ~depth_limit:2048 projection in
  let a = assertions () in
  typed_guard (fun v x -> v#visit_assertion () x) a;
  let allowed = ref [] in
  let visitor = object
    inherit [_] Visitors.iter as super
    method! visit_literal env literal = match literal with
      | Literal.Int z ->
          let bits = Z.numbits z in
          require (bits <= 65536) "state-integer-bit-cap";
          let raw = Obj.repr z in
          if not (Obj.is_int raw) then allowed := (raw, bits) :: !allowed
      | _ -> super#visit_literal env literal
  end in
  visitor#visit_assertion () a;
  let used = ref 0 in
  List.iter (fun raw ->
    match List.find_opt (fun (known, _) -> raw == known) !allowed with
    | None -> raise (C.Incomplete "unaccounted-serialized-state-custom-block")
    | Some (_, bits) ->
        used := !used + max 1 bits;
        require (!used <= 1048576) "state-integer-conversion-cap";
        charge_integer bits) customs;
  let json = to_json () in C.guard_transport json; json
let snapshot origin ~id ~phase payload = Option.iter (fun o -> observe (fun s ->
  require(Option.is_none s.snapshot)"v4-field-callback-required";
  with_origin_context s phase o (fun () ->
  require (not s.alternative || all_groups_closed s) "snapshot-before-group-closure";
  let public_id, normalized_id = id in
  let update () =
    if phase = "normalized-state" then o.states <- o.states + 1
    else if phase = "test-created" then o.tests <- o.tests + 1 in
  (if phase = "normalized-state" then
     require (normalized_id = o.states) "normalized-ordinal-gap"
   else if phase = "test-created" then
     require (normalized_id = o.tests && normalized_id = o.states - 1 &&
       o.to_verify = Some true) "duplicate-or-unbound-native-test");
  if not s.framed then update ();
  emit_choice s phase (fun () -> `Assoc (origin_fields o @
    ["native_id", `List [`Int public_id; `Int normalized_id];
     "pred_defs_ref", `String "this-session-current-preprocessed-program";
     "payload", payload ()]))
    (F.fields(stream_origin o @
      ["native_id",F.values [F.int public_id;F.int normalized_id];
       "pred_defs_ref",F.bytes "this-session-current-preprocessed-program";
       "payload",stream_leaf payload]));
  if s.framed then update ()))) origin


(* Only actual Verifier v4 callbacks enter this API. Legacy snapshot remains
   unchanged above, including its original materialization/admission order. *)
let snapshot_fields origin ~id ~phase ~prepare fields = Option.iter(fun o -> observe(fun s ->
  with_origin_context s phase o(fun()->
  require(all_groups_closed s)"v4-snapshot-before-group-closure";
  let public,ordinal=id in
  if phase="normalized-state"then require(ordinal=o.states)"normalized-ordinal-gap"
  else require(phase="test-created"&&ordinal=o.tests&&ordinal=o.states-1&&o.to_verify=Some true)
    "duplicate-or-unbound-native-test";
  let dictionary=match s.snapshot with Some d->d|None->raise(C.Incomplete"v4-profile-required")in
  let previous= !integer_bits in
  Fun.protect ~finally:(fun()->integer_bits:=previous)(fun()->
    integer_bits:=Some(ref 0);
    emit_framed ~body:(fun put ->
      (* prepare retains actual substitution guards inside the ONE shared Z
         budget, before any field serializer or closed-value reuse. *)
      prepare();
      Snapshot.emit dictionary ~sequence:s.logical_events ~source:(snapshot_source_index s o.source) ~phase
        ~kind:o.source.kind ~name:o.source.name ~parent:o.raw_parent
        ~alternative:o.alternative ~expanded:o.expanded ~native:(public,ordinal)
        ~fields ~integer_bits:(fun()->match !integer_bits with Some x-> !x|None->assert false) ~put)
      s phase (fun _->assert false));
  if phase="normalized-state"then o.states<-o.states+1 else o.tests<-o.tests+1)))origin

let make ?(snapshot_observations=false) ?(framed=false) ?(alternative=false) ?(field_framed=false) ?(bytes=max_bytes) ?(events=max_events) ?(record=max_record)
    ?(carriers=max_carriers) ~path ~identity ~sink ~close ~receipt () =
  let alternative=alternative || field_framed in
  let framed = framed || alternative in
  {path; identity; sink; close; receipt;
   byte_cap = min max_bytes (max 0 bytes); event_cap = min max_events (max 0 events);
   record_cap = min max_record (max 0 record);
   carrier_cap = min max_carriers (max 0 carriers);
   bytes = 0; events = 0; failed = None; framed; alternative;
   snapshot=(if field_framed then Some(Snapshot.create ~observations:snapshot_observations())else None);group_open=false; logical_events=0; terminal = false; closed = false;
   sources = []; origins = []; prepared_inputs=[];
   preparation_stage_started=false; preparation_stage_complete=false;
   procedures = SS.empty; lemmas = SS.empty}
let receipt path identity complete reason =
  Printf.eprintf
    "PREPARATION_PROVENANCE path=%S session=%S complete=%b reason=%S\n%!"
    path identity complete reason
let open_runtime path =
  let identity = Printf.sprintf "%d-%.6f" (Unix.getpid ()) (Unix.gettimeofday ()) in
  let report = receipt (if String.length path <= 4096 then path else "<oversized-path>") identity in
  try
    let framed,alternative,field_framed=match Sys.getenv_opt "GILLIAN_PREPARATION_PROVENANCE_TRANSPORT" with
      | None | Some "v1" -> false,false,false | Some "byte-framed-v2" -> true,false,false
      | Some "alternative-framed-v3" -> true,true,false
      | Some "field-framed-v4" -> true,true,true
      | Some _ -> raise(C.Incomplete "unknown-preparation-transport-profile") in
    require (String.length path <= 4096 && not (Filename.is_relative path) &&
      not (String.contains path '\000')) "absolute-bounded-capture-path";
    let parent = Filename.dirname path and leaf = Filename.basename path in
    require (leaf <> "." && leaf <> ".." &&
      path = Filename.concat parent leaf && Unix.realpath parent = parent)
      "canonical-capture-parent";
    let parent_stat = Unix.lstat parent in
    require (parent_stat.Unix.st_kind = Unix.S_DIR &&
      parent_stat.st_uid = Unix.geteuid () && parent_stat.st_perm land 0o077 = 0)
      "private-owned-capture-parent";
    let same_inode a b = a.Unix.st_dev = b.Unix.st_dev && a.st_ino = b.st_ino in
    let fd = Unix.openfile path [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL] 0o600 in
    (try
       let opened = Unix.fstat fd and named = Unix.lstat path in
       require (same_inode opened named && opened.st_kind = Unix.S_REG &&
         opened.st_uid = Unix.geteuid () && opened.st_perm land 0o777 = 0o600 &&
         opened.st_nlink = 1 && opened.st_size = 0 &&
         same_inode parent_stat (Unix.lstat parent) && Unix.realpath parent = parent)
         "fresh-capture-file-and-parent-identity"
     with exn -> Unix.close fd; raise exn);
    let sink text =
      let rec write at = if at < String.length text then (
        let n = Unix.write_substring fd text at (String.length text - at) in
        require (n > 0) "zero-write-progress"; write (at + n)) in
      write 0 in
    let close () =
      Fun.protect ~finally:(fun () -> Unix.close fd)
        (fun () ->
          Unix.fsync fd;
          require (same_inode (Unix.fstat fd) (Unix.lstat path) &&
            same_inode parent_stat (Unix.lstat parent) &&
            Unix.realpath parent = parent) "capture-final-named-identity") in
    (try Some (make ~framed ~alternative ~field_framed ~path ~identity ~sink ~close ~receipt:report ())
     with exn -> Unix.close fd; raise exn)
  with _ -> (try report false "fresh-output-open-failed" with _ -> ()); None
let initialise_v1 s prog =
  let procedures, lemmas = select_procs_and_lemmas
    ~procs_to_verify:(SS.of_list (Prog.get_noninternal_proc_names prog))
    ~lemmas_to_verify:(SS.of_list (Prog.get_noninternal_lemma_names prog)) in
  s.procedures <- procedures; s.lemmas <- lemmas;
  emit s "start" (fun () -> `Assoc
    ["path", `String s.path; "procedures", `List (List.map (fun n -> `String n) (SS.elements procedures));
     "lemmas", `List (List.map (fun n -> `String n) (SS.elements lemmas));
     "source_stage", `String "fully-linked-preprocess-entry";
     "caps", `List [`Int s.byte_cap; `Int s.event_cap; `Int s.record_cap; `Int s.carrier_cap]]);
  SS.iter (fun name ->
    let proc = Prog.get_proc_exn prog name in
    let spec = match proc.proc_spec with Some x -> x
      | None -> raise (C.Incomplete "selected-procedure-has-no-original-spec") in
    ignore (inspect_aggregate Original_procs spec.spec_sspecs);
    let source = add_source s "procedure" name (List.length spec.spec_sspecs) in
    List.iteri (fun ordinal (c : Spec.st) -> emit s "original-parent" (fun () ->
      `Assoc (source_fields source @ ["raw_parent", `Int ordinal;
       "parent_count", `Int (Array.length source.groups);
       "parameters", (C.guard_plain spec.spec_params;
         `List (List.map (fun p -> `String p) spec.spec_params));
       "raw_arguments", (C.guard_plain spec.spec_raw_args;
         match spec.spec_raw_args with None -> `Null | Some names ->
           `List (List.map (fun name -> `String name) names));
       "spec_to_verify", `Bool spec.spec_to_verify;
       "source_path", (C.guard_plain proc.proc_source_path;
         match proc.proc_source_path with None -> `Null | Some p -> `String p);
       "source_location", (match spec.spec_location with None -> `Null
         | Some l -> C.guard_plain l; Location.to_yojson l);
       "pre", located c.ss_pre; "posts", posts c.ss_posts;
       "variant", optional_expr c.ss_variant;
       "flag", Flag.to_yojson c.ss_flag;
       "to_verify", `Bool c.ss_to_verify;
       "label", (C.guard_plain c.ss_label;
         match c.ss_label with None -> `Null | Some (n, xs) ->
           `List [`String n; `List (List.map (fun x -> `String x) xs)]);
       "verifier_scope", (match c.ss_verifier_scope with None -> `Null
         | Some b -> `List [expr b.vsb_source; expr b.vsb_target])]))) spec.spec_sspecs) procedures;
  SS.iter (fun name ->
    let lemma = Prog.get_lemma_exn prog name in
    ignore (inspect_aggregate Original_lemmas lemma.lemma_specs);
    let source = add_source s "lemma" name (List.length lemma.lemma_specs) in
    List.iteri (fun ordinal (c : Lemma.spec) -> emit s "original-parent" (fun () ->
      `Assoc (source_fields source @ ["raw_parent", `Int ordinal;
       "parent_count", `Int (Array.length source.groups);
       "parameters", (C.guard_plain lemma.lemma_params;
         `List (List.map (fun p -> `String p) lemma.lemma_params));
       "source_path", (C.guard_plain lemma.lemma_source_path;
         match lemma.lemma_source_path with None -> `Null | Some p -> `String p);
       "source_location", (match lemma.lemma_location with None -> `Null
         | Some l -> C.guard_plain l; Location.to_yojson l);
       "pre", located c.lemma_hyp; "posts", posts c.lemma_concs;
       "variant", optional_expr c.lemma_spec_variant]))) lemma.lemma_specs) lemmas
(* v2 deliberately duplicates only the fixed outer metadata schema. Every
   original parent and ordered occurrence has the same logical representation. *)
let framed_parents s ~event ~prepared procs lemmas =
  let stage_source kind name values =
    if not prepared then add_source s kind name (List.length values)
    else (
      let source=match find_source s kind name with Some source -> source
        | None -> raise(C.Incomplete "pre-expansion-missing-original-source") in
      let rec exact remaining = function
        | [] -> require (remaining=0) "pre-expansion-parent-count-drift"
        | _::rest -> require (remaining>0) "pre-expansion-parent-count-drift";
            exact (remaining-1) rest in
      exact (Array.length source.groups) values;source) in
  let remember source ordinal input =
    require (not(List.exists(fun (prior,index,_) -> prior==source && index=ordinal)
      s.prepared_inputs)) "duplicate-pre-expansion-parent";
    (* Identity pin to the immutable located input at this exact boundary;
       no graph copy, AST comparison or extra serialization. Reader separately
       binds the complete tagged input bytes to this stage's fingerprint. *)
    s.prepared_inputs <- (source,ordinal,Obj.repr input)::s.prepared_inputs in
  let capture source ordinal f =
    if s.alternative then v3_context event source.kind source.name
      ordinal (-1) f else f () in
  let parameters xs t = C.guard_plain xs;
    F.list(fun add -> List.iter(fun p -> add(F.bytes p))xs)t in
  let path p t = C.guard_plain p;
    (match p with None -> F.null | Some p -> F.bytes p)t in
  SS.iter(fun name ->
    let proc : (_,_) Proc.t=Hashtbl.find procs name in
    let spec=match proc.proc_spec with Some x -> x
      | None -> raise(C.Incomplete "selected-procedure-has-no-original-spec") in
    if not prepared then ignore(inspect_aggregate Original_procs spec.spec_sspecs);
    let source=stage_source "procedure" name spec.spec_sspecs in
    List.iteri(fun ordinal (c:Spec.st) -> capture source ordinal (fun () ->
      if prepared then ignore(inspect_aggregate Expanded_parent (c.ss_pre,c.ss_posts));
      let label t = C.guard_plain c.ss_label;
        (match c.ss_label with None -> F.null | Some(n,xs) ->
         F.values[F.bytes n;F.list(fun add -> List.iter(fun x -> add(F.bytes x))xs)])t in
      emit_framed s event (F.fields(stream_source source @[
        "raw_parent",F.int ordinal;"parent_count",F.int(Array.length source.groups);
        "parameters",parameters spec.spec_params;
        "raw_arguments",(match spec.spec_raw_args with None -> F.null | Some names -> parameters names);
        "spec_to_verify",F.bool spec.spec_to_verify;
        "source_path",path proc.proc_source_path;
        "source_location",stream_location spec.spec_location;
        "pre",stream_located c.ss_pre;"posts",stream_posts c.ss_posts;
        "variant",stream_optional_expr c.ss_variant;
        "flag",stream_leaf(fun () -> Flag.to_yojson c.ss_flag);
        "to_verify",F.bool c.ss_to_verify;"label",label;
        "verifier_scope",(match c.ss_verifier_scope with None -> F.null | Some b ->
          F.values[stream_expr b.vsb_source;stream_expr b.vsb_target])]));
      if prepared then remember source ordinal c.ss_pre))spec.spec_sspecs)s.procedures;
  SS.iter(fun name ->
    let lemma : Lemma.t=Hashtbl.find lemmas name in
    if not prepared then ignore(inspect_aggregate Original_lemmas lemma.lemma_specs);
    let source=stage_source "lemma" name lemma.lemma_specs in
    List.iteri(fun ordinal (c:Lemma.spec) -> capture source ordinal (fun () ->
      if prepared then ignore(inspect_aggregate Expanded_parent (c.lemma_hyp,c.lemma_concs));
      emit_framed s event (F.fields(stream_source source @[
        "raw_parent",F.int ordinal;"parent_count",F.int(Array.length source.groups);
        "parameters",parameters lemma.lemma_params;"source_path",path lemma.lemma_source_path;
        "source_location",stream_location lemma.lemma_location;
        "pre",stream_located c.lemma_hyp;"posts",stream_posts c.lemma_concs;
        "variant",stream_optional_expr c.lemma_spec_variant] @
        (if s.alternative then ["declaration_variant",stream_optional_expr lemma.lemma_variant] else [])));
      if prepared then remember source ordinal c.lemma_hyp))lemma.lemma_specs)s.lemmas
let initialise_framed s prog =
  let procedures,lemmas=select_procs_and_lemmas
    ~procs_to_verify:(SS.of_list(Prog.get_noninternal_proc_names prog))
    ~lemmas_to_verify:(SS.of_list(Prog.get_noninternal_lemma_names prog)) in
  s.procedures<-procedures;s.lemmas<-lemmas;
  let names ns=F.list(fun add -> SS.iter(fun n -> add(F.bytes n))ns) in
  emit_framed s "start" (F.fields[
    "path",F.bytes s.path;"procedures",names procedures;"lemmas",names lemmas;
    "source_stage",F.bytes "fully-linked-preprocess-entry";
    "caps",F.values[F.int s.byte_cap;F.int s.event_cap;F.int s.record_cap;F.int s.carrier_cap]]);
  framed_parents s ~event:"original-parent" ~prepared:false prog.Prog.procs prog.Prog.lemmas
(* Called once by the actual frontend, with the CURRENT transformed tables.
   V1/default and v2 are passive here: neither tables nor payloads are touched. *)
let before_expansion ~procs ~lemmas = observe (fun s -> if s.alternative then (
  require (not s.preparation_stage_started && s.origins=[] && not s.group_open)
    "duplicate-or-late-pre-expansion-stage";
  s.preparation_stage_started<-true;
  framed_parents s ~event:"pre-expansion-parent" ~prepared:true procs lemmas;
  require (List.length s.prepared_inputs=List.fold_left (fun n source ->
    n+Array.length source.groups) 0 s.sources) "incomplete-pre-expansion-stage";
  s.preparation_stage_complete<-true))
let initialise s prog =
  if s.framed then initialise_framed s prog else initialise_v1 s prog
let with_preprocess prog action =
  (match Sys.getenv_opt "GILLIAN_PREPARATION_PROVENANCE_PATH" with
   | None -> ()
   | Some path ->
       (match !current with
        | Some s -> fail s "error" "repeated-preprocess-session"
        | None -> current := open_runtime path));
  observe (fun s -> initialise s prog);
  match action () with
  | result -> result
  | exception exn -> observe (fun s -> fail s "error" "preprocessing-exception"); raise exn
let preprocessed prog ~unfold =
  if not unfold then observe (fun s ->
    SS.iter (fun name ->
      let proc = Prog.get_proc_exn prog name in
      Option.iter (fun spec -> List.iteri (fun i (c : Spec.st) ->
        spec_group name i c.ss_pre [c]) spec.Spec.spec_sspecs) proc.proc_spec) s.procedures;
    SS.iter (fun name ->
      let lemma = Prog.get_lemma_exn prog name in
      List.iteri (fun i (c : Lemma.spec) ->
        lemma_group name i c.lemma_hyp [c]) lemma.lemma_specs) s.lemmas);
  observe (fun s -> require (List.for_all (fun source ->
    Array.for_all Fun.id source.groups) s.sources) "missing-expanded-parent")
let preparing ~procedures ~lemmas action =
  observe (fun s -> require (not s.alternative || all_groups_closed s)
    "preparation-before-group-closure");
  observe (fun s -> require (SS.equal procedures s.procedures &&
    SS.equal lemmas s.lemmas) "final-selection-differs-from-source-selection");
  match action () with
  | result -> result
  | exception exn -> observe (fun s -> fail s "error" "test-preparation-exception"); raise exn
let finish ~procedure_tests ~lemma_tests = observe (fun s ->
  require (not s.alternative || s.preparation_stage_complete) "unfinished-pre-expansion-stage";
  require (not s.alternative || not s.group_open) "unfinished-open-parent-group";
  require (List.for_all (fun source -> Array.for_all Fun.id source.groups) s.sources)
    "unfinished-parent-groups";
  require (List.for_all (fun o -> o.begun && o.normalised = Some o.states &&
    match o.to_verify with Some true -> o.tests = o.states
      | Some false -> o.tests = 0 | None -> false) s.origins)
    "unfinished-expanded-carriers";
  let count kind = List.fold_left (fun n o ->
    if o.source.kind = kind then n + o.tests else n) 0 s.origins in
  require (count "procedure" = procedure_tests && count "lemma" = lemma_tests)
    "native-test-total-mismatch";
  let text = Yojson.Safe.to_string (envelope s "end" true
    ((if s.framed then ["logical_events",`Int s.logical_events] else []) @
    ["raw_parents", `Int (List.fold_left (fun n x -> n + Array.length x.groups) 0 s.sources);
     "expanded", `Int (List.length s.origins);
     "normalized_states", `Int (List.fold_left (fun n o -> n + o.states) 0 s.origins);
     "procedure_tests", `Int procedure_tests; "lemma_tests", `Int lemma_tests;
     "total_tests", `Int (procedure_tests + lemma_tests)])) ^ "\n" in
  require (String.length text <= terminal_reserve && s.events < s.event_cap &&
    s.bytes + String.length text <= s.byte_cap) "terminal-reserve-exhausted";
  output s text;
  close s; (* A written end alone is insufficient: the bound receipt is required. *)
  s.terminal <- true; s.receipt true "closed-complete")
let () = at_exit (fun () -> match !current with
  | Some s when not s.terminal -> fail s "error" "process-exit-before-completion"
  | _ -> ())

module For_tests = struct
  let run ?framed ?alternative ?field_framed ?bytes ?events ?record ?carriers
      ?(path="/test/provenance") ?(identity="test-session") sink f =
    let previous = !current in
    let receipts = ref [] in
    let s = make ~snapshot_observations:true ?framed ?alternative ?field_framed ?bytes ?events ?record ?carriers ~path ~identity ~sink ~close:(fun () -> ())
      ~receipt:(fun ok reason -> receipts := (ok, reason) :: !receipts) () in
    current := Some s;
    Fun.protect ~finally:(fun () -> current := previous) (fun () ->
      let result = f s in result, s, List.rev !receipts)
end
