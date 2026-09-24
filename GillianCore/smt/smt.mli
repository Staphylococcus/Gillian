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

(** True only for native UNSAT. SAT or unknown is inconclusive and returns
    false; it must not be used as a SAT/branch-feasibility decision. Other
    solver errors, including invalid models, propagate. Unknown is never cached.
    This optional search is capped at five seconds and the configured SMT limit.
*)
val proves_unsat : Expr.Set.t -> (string, Type.t) Hashtbl.t -> bool

(** Complete-query feasibility, with a bounded existential witness search for
    total-mode queries with multiple UTF-16 and Number variables. Guesses never
    enter symbolic state; only native validated SAT can succeed early.
    UNSAT/unknown falls back to the original query, whose unknown/error policy
    remains unchanged. *)
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
