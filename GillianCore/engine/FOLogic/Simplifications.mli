(** Release only simplification memo entries after a complete verification case.
    This does not change live PFS/Gamma/substitutions or fresh identities. *)
val clear_cache : unit -> unit

(** [simplify_pfs_and_gamma ?matching ?kill_new_lvars ?save_spec_vars
     ?existentials lpfs ?rpfs gamma] simplifies the pure formule [lpfs] and the
    typing environment [gamma], attempting to instantiate the (optional)
    [existentials] and returning the learned bindings and a (possibly smaller)
    new set of existentials. If provided, it will also try to simplify the pure
    formule [rpfs], assuming that that they are in the context of the entailment
    << ∃ [existentials]. [lpfs] => [rpfs] >>. If the [kill_new_lvars] flag is
    set, the logical variables introduced by the simplification will be removed
    if learned during the simplification, and kept otherwise. If the
    [save_spec_vars] parameter is not provided, all learned spec variables will
    be removed. If the [save_spec_vars] parameter is [(_, true)], all spec
    variables will be preserved. If the [save_spec_vars] parameter is
    [(var_set, false)], only the spec variables in [var_set] will be preserved.
    The [matching] flag should not be used by Gillian instantiation developers.
    [on_false] observes an existing contradiction reason. Only literal-false
    reduction supplies its local before/after pair; neither is an original
    caller-atom provenance claim. Callback errors do not affect simplification.
*)
val simplify_pfs_and_gamma :
  ?matching:bool ->
  ?on_false:(string -> (Expr.t * Expr.t) option -> unit) ->
  ?kill_new_lvars:bool ->
  ?save_spec_vars:Utils.Containers.SS.t * bool ->
  ?existentials:Utils.Containers.SS.t ->
  PFS.t ->
  ?rpfs:PFS.t ->
  Type_env.t ->
  SVal.SESubst.t * Utils.Containers.SS.t

(** [simplify_implication existentials lpfs rpfs gamma] simplifies the
    entailment << ∃ [existentials]. [lpfs] => [rpfs] >> under the typing
    environment [gamma], attempting to instantiate the [existentials] and
    returning a (possibly smaller) new set of existentials *)
val simplify_implication :
  ?on_false:(string -> (Expr.t * Expr.t) option -> unit) ->
  matching:bool ->
  Utils.Containers.SS.t ->
  PFS.t ->
  PFS.t ->
  Type_env.t ->
  Utils.Containers.SS.t

(** [admissible_assertion a] checks whether or not the assertion [a] is a
    contradiction only using the reductions/simplifications *)
val admissible_assertion : Gil_syntax.Asrt.t -> bool
