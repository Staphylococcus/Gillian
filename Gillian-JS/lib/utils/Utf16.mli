(** Decode Flow's WTF-8 strings into JavaScript UTF-16 code units. Malformed
    internal encodings raise Unsupported rather than substituting characters. *)
val code_units : string -> int list

val of_code_units : int list -> string
val canonical : string -> string

(** Convert paired code units to scalar UTF-8. Raw lone surrogates in generated
    source are unsupported by Flow and raise Unsupported before parsing. *)
val source_text : string -> string

val trim : string -> string
