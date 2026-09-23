open Gillian.Concrete

type t

val pp : Format.formatter -> string * t * Values.t -> unit
val init : unit -> t
val get : t -> Gillian.Gil_syntax.Literal.t -> Values.t option
val set : t -> Gillian.Gil_syntax.Literal.t -> Values.t -> unit
val remove : t -> Gillian.Gil_syntax.Literal.t -> unit
val properties : t -> Gillian.Gil_syntax.Literal.t list
