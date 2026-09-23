(** Decode Flow's WTF-8 strings into JavaScript UTF-16 code units. Malformed
    internal encodings raise Unsupported rather than substituting characters. *)
val code_units : string -> int list

val of_code_units : int list -> string
val canonical : string -> string

(** A finite code-unit value, stored as canonical CESU-8. Construction validates
    the domain; concatenation preserves it by the codec's concatenation law. *)
type t

val of_canonical : string -> t
val to_canonical : t -> string
val equal : t -> t -> bool
val compare : t -> t -> int
val concat : t -> t -> t
val length : t -> int
val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (t, string) result

(** Convert paired code units to scalar UTF-8. Raw lone surrogates in generated
    source are unsupported by Flow and raise Unsupported before parsing. *)
val source_text : string -> string

val trim : string -> string
