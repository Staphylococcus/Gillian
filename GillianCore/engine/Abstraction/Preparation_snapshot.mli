(** Capture-only v4 dictionary. No native object/AST is retained here. *)
type t
val create : ?observations:bool -> unit -> t
val append : t -> string -> unit
val position : t -> int
val release : t -> unit
val commit : t -> sequence:int -> unit
val remember_import : t -> sequence:int -> origin:string -> role:string ->
  offset:int -> bytes:int -> Yojson.Safe.t -> unit
val origin_key : source:int -> parent:int -> alternative:int -> expanded:int -> string
val emit : t -> sequence:int -> source:int -> phase:string -> kind:string -> name:string ->
  parent:int -> alternative:int -> expanded:int -> native:int * int ->
  fields:(string * (unit -> Yojson.Safe.t)) list ->
  integer_bits:(unit -> int) -> put:(string -> unit) -> unit
val completed : t -> Yojson.Safe.t list
module For_tests : sig
  val sha256 : string -> string
  val committed_definitions : t -> int
  val with_field_observer :
    (phase:string -> kind:string -> name:string -> parent:int -> alternative:int ->
      expanded:int -> native:(int * int) -> role:string -> Yojson.Safe.t -> unit) ->
    (unit -> 'a) -> 'a
  val shape : Yojson.Safe.t -> int list
end
