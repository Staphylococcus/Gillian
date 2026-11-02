(** Diagnostic sidecar only. Callbacks are inert outside the focused root.
    State IDs name read-only physical scope-entry objects, not proof counters or
    a replacement for native FS/Gamma. Missing/overflowed records cannot qualify
    lineage. No tuple is truncated and presented as complete. *)
val active : unit -> bool
val focused : string -> bool
val event : string -> state:'s -> (unit -> Yojson.Safe.t) -> unit
val scope : string -> state:'s -> (unit -> Yojson.Safe.t) -> (unit -> 'a) -> 'a
val scope_if : bool -> string -> state:'s -> (unit -> Yojson.Safe.t) -> (unit -> 'a) -> 'a
val with_root : target:string -> case_id:int * int -> state:'s -> (unit -> 'a) -> 'a
val query : query:string -> caller:string -> unit
module For_tests : sig
  val run : ?enabled:bool -> ?bytes:int -> ?events:int -> ?event_bytes:int ->
    (string -> unit) -> (unit -> 'a) -> 'a * bool
end
