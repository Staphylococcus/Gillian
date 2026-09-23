(** A separate native code-unit view. Generic GIL strings remain byte strings;
    this bridge does not by itself admit symbolic JS strings or operations. *)
val sort : Sexplib.Sexp.t

(** Encode canonical CESU-8 as [(Seq (_ BitVec 16))]. Malformed WTF-8 and valid
    but noncanonical encodings raise [Utils.Exceptions.Unsupported]. Callers
    must establish the JS value domain before using this view. *)
val encode : string -> Sexplib.Sexp.t

(** Recover a concrete native sequence model as canonical CESU-8. Accepts typed
    empty sequences, 16-bit hex/binary units, concatenations and lets. Wrong
    widths/sorts, malformed or unevaluated terms return [None], never an empty
    or replacement string. *)
val recover : Sexplib.Sexp.t -> string option
