open Gil_syntax
module Utf16 : module type of Utf16_encoding

exception SMT_unknown
exception SMT_error of string

(** Native Z3 phase policy controls search order only. Default 3 matches Z3; an
    explicit override is useful for exact solver-defect reproductions. *)
val exec_sat :
  ?phase_selection:int ->
  Expr.Set.t ->
  (string, Type.t) Hashtbl.t ->
  Sexplib.Sexp.t option

val is_sat : Expr.Set.t -> (string, Type.t) Hashtbl.t -> bool

val check_sat :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Sexplib.Sexp.t option

val lift_model :
  Sexplib.Sexp.t ->
  (string, Type.t) Hashtbl.t ->
  (string -> Expr.t -> unit) ->
  Expr.Set.t ->
  unit

val pp_sexp : Sexplib.Sexp.t Fmt.t
