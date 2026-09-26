open Gil_syntax
module Utf16 : module type of Utf16_encoding

exception SMT_unknown
exception SMT_error of string

(** Native model together with its originating datatype declarations, retained
    across solver resets and cache hits. *)
type model

(** Native Z3 phase policy controls search order only. Default 3 matches Z3; an
    explicit override is useful for exact solver-defect reproductions. *)
val exec_sat :
  ?phase_selection:int ->
  Expr.Set.t ->
  (string, Type.t) Hashtbl.t ->
  model option

(** True only for native UNSAT. SAT or unknown is inconclusive and returns
    false; it must not be used as a SAT/branch-feasibility decision. Other
    solver errors, including invalid models, propagate. An inconclusive optional
    attempt is remembered only to avoid repeating it; it is never stored as a
    SAT/UNSAT decision or used by required queries. Actual cached decisions take
    precedence. Each optional search is capped at five seconds and the SMT
    limit. *)
val proves_unsat : Expr.Set.t -> (string, Type.t) Hashtbl.t -> bool

(** Complete-query satisfiability, with bounded existential witness searches for
    eligible UTF-16/Number queries. Before any witness search, a total-mode
    mixed UTF-16/Number query first runs a sufficient native UNSAT precheck on a
    proper nonempty unchanged numeric subset of the original top-level
    expressions; a native UNSAT answer for that subset proves the whole
    conjunction unsatisfiable and returns None without executing the complete
    mixed query. A numeric SAT/unknown answer proves nothing about feasibility
    and falls through to the pre-existing complete-query path unchanged. A
    validated full-query model is a witness; numeric index identities are added
    only after a native UNSAT proof from original integrality facts. The
    required query retains every original fact; failed optional attempts retain
    its original unknown/error policy. No guess or unproved identity replaces
    symbolic-state facts. *)
val check_sat : Expr.Set.t -> (string, Type.t) Hashtbl.t -> model option

(** Boolean view of [check_sat], including the same cache and witness search. *)
val is_sat : Expr.Set.t -> (string, Type.t) Hashtbl.t -> bool

val lift_model :
  model ->
  (string, Type.t) Hashtbl.t ->
  (string -> Expr.t -> unit) ->
  Expr.Set.t ->
  unit

val pp_sexp : Sexplib.Sexp.t Fmt.t
val pp_model : model Fmt.t
