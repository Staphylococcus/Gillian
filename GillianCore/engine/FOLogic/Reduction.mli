(** [ReductionException (e, msg)] denotes an exception raised due to an
    expression [e] being malformed with explanation [msg] *)
exception ReductionException of Gil_syntax.Expr.t * string

(** Internal diagnostic observer, enabled only by the startup environment flag.
    Snapshots are independent copies; reset clears counters only, retaining the
    sticky incomplete flag and the process-wide reporting budget. *)
type preparation_profile_counter = {
  started : int; completed : int; hits : int; size_min : int; size_max : int;
  samples : int; cpu_sum : float; cpu_max : float; cpu_zero : int;
}

type preparation_profile_snapshot = {
  enabled : bool;
  membership : preparation_profile_counter array array;
  copies : preparation_profile_counter array;
  counter_resets : int;
  periodic_reports : int;
  final_report_requested : bool;
  report_payload_bytes : int;
  incomplete : bool;
}

val preparation_profile_enabled : bool
val preparation_profile_reset : unit -> unit
val preparation_profile_snapshot : unit -> preparation_profile_snapshot
val preparation_profile_dump : ?final:bool -> unit -> unit

(** [resolve_to_location pfs e] attempts to resolve the expression denoted by
    [e] to a location given the pure formulae [pfs]. If successful, it returns
    that location, together with any bindings learned during the resolution. *)
val resolve_expr_to_location :
  PFS.t -> Type_env.t -> Gil_syntax.Expr.t -> string option

(** [get_equal_expressions pfs e] returns a list of expressions that equal [e]
    under the pure formulae [pfs]. *)
val get_equal_expressions : PFS.t -> Gil_syntax.Expr.t -> Gil_syntax.Expr.t list

val understand_lstcat :
  PFS.t ->
  Type_env.t ->
  Expr.t list ->
  Expr.t list ->
  (Expr.t * Containers.SS.t) option

(** [reduce_lexpr ?matching ?reduce_lvars ?pfs ?gamma e] reduces the expression
    [e] given (optional) pure formulae [pfs] and typing environment [gamma]. The
    [reduce_lvars] and [matching] flags should not be used by Gillian
    instantiation developers. *)
val reduce_lexpr :
  ?matching:bool ->
  ?reduce_lvars:bool ->
  ?pfs:PFS.t ->
  ?gamma:Type_env.t ->
  Gil_syntax.Expr.t ->
  Gil_syntax.Expr.t

(** Internal ordered sanitizer map pass. Reduces every root against its live
    PFS, using a pass-local exact structural membership index. Generic roots
    retain the original per-root frozen typing-environment copy. *)
val reduce_pfs_in_place : ?matching:bool -> Type_env.t -> PFS.t -> unit

(** Internal append-only overlap pass. Classifies each guard in matching mode
    against earlier actual insertions; drops only literal true without inferred
    typing. Retains original guard objects, duplicate behavior and order, using
    one private exact membership set. Discards the set before later sanitation. *)
val extend_pfs_with_overlap_guards : Type_env.t -> PFS.t -> Expr.t list -> unit

(** Internal complete filter pass. Operations are bound to this live PFS;
    callers must route mapper mutations through them. The private lazy index
    respects delayed unlinking and is discarded before later fixed-point work. *)
type formula_filter_ops = {
  reduce_formula : Expr.t -> Expr.t;
  extend : Expr.t -> unit;
  substitute : SVal.SESubst.t -> unit;
  substitute_expr : Expr.t -> Expr.t -> unit;
}

val filter_map_pfs_with_live_reduction :
  ?matching:bool -> Type_env.t -> PFS.t ->
  (formula_filter_ops -> Expr.t -> [ `Stop | `Replace of Expr.t | `Filter ]) -> bool

(** [reduce_assertion ?matching ?pfs ?gamma a] reduces the assertion [a] given
    (optional) pure formulae [pfs] and typing environment [gamma]. The
    [matching] flag should not be used by Gillian instantiation developers. *)
val reduce_assertion :
  ?matching:bool ->
  ?pfs:PFS.t ->
  ?gamma:Type_env.t ->
  Gil_syntax.Asrt.t ->
  Gil_syntax.Asrt.t

val is_tautology : ?pfs:PFS.t -> ?gamma:Type_env.t -> Gil_syntax.Expr.t -> bool
