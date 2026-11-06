(** [check_satisfiability_with_model pfs gamma] checks whether or not the pure
    formulae [pfs] are satisfiable under the typing environment [gamma]. If this
    is the case, the function returns the appropriate logical environment. *)
val check_satisfiability_with_model :
  Gil_syntax.Expr.t list -> Type_env.t -> SVal.SESubst.t option

(** Pure nonmutating query enrichment, not a proof. Returns enriched facts,
    added identities, original/current formatter atoms and licensing premises. *)
val positive_finite_numeric_identity_satisfiability :
  Expr.t list ->
  Type_env.t ->
  Expr.Set.t ->
  Type_env.t ->
  (Expr.Set.t * Expr.t list * Expr.t list * Expr.t list * Expr.t list * Expr.t list)
  option

(** [check_satisfiability ?matching pfs gamma] checks whether or not the pure
    formulae [pfs] are satisfiable under the typing environment [gamma]. The
    [matching] flag should not be used by Gillian instantiation developers. *)
val check_satisfiability :
  ?matching:bool ->
  ?time:string ->
  ?relevant_info:Containers.SS.t * Containers.SS.t * Containers.SS.t ->
  Gil_syntax.Expr.t list ->
  Type_env.t ->
  bool

(** A different API for [check_satisfiability] better adapted for usage in
    memory models *)
val sat :
  matching:bool -> pfs:PFS.t -> gamma:Type_env.t -> Gil_syntax.Expr.t -> bool

(** [check_entailment existentials lpfs rpfs gamma] checks whether or not the
    entailment << ∃ [existentials]. [lpfs] => [rpfs] >> holds under the typing
    environment [gamma]. *)
(** Select only original, typed integer order facts for a sufficient UNSAT
    query. None leaves ordinary entailment unchanged; no input is mutated. *)
val integer_order_core :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.t -> Expr.Set.t option

(** Select only original facts for finite Number-difference bounds. This pure
    selector does not prove them; its caller still requires native UNSAT. *)
val finite_difference_core :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.t -> Expr.Set.t option

(** Bounded connected component of exact scalar numeric atoms. Selection is
    only a weakening; it changes no input and requires native UNSAT. *)
val numeric_component_core :
  existentials:Containers.SS.t ->
  original_gamma:(string, Type.t) Hashtbl.t ->
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.t -> Expr.Set.t option

(** Pure original-fact selector/projection for the guarded sequence-count
    obligation. Selection proves nothing; the caller must still obtain actual
    native UNSAT. Neither source formulae nor either Gamma is mutated. *)
val sequence_count_projection :
  reserved_names:Containers.SS.t Lazy.t ->
  original_gamma:(string, Type.t) Hashtbl.t ->
  Expr.Set.t ->
  (string, Type.t) Hashtbl.t ->
  Expr.t ->
  (Expr.Set.t * Expr.Set.t * (string, Type.t) Hashtbl.t * (Expr.t * string) list) option

(** For a guarded numeric counter or its exact +1 successor, retain all
    original type/range gates, then prefer original literal Int bounds on the
    identical count in the opposite direction to the counterquery (including
    Not). Otherwise select the same four original atoms with a strict/inclusive
    array upper bound. Pure selection changes no input and proves nothing
    without native UNSAT; the historical successor-bound name is unchanged. *)
val successor_bound_core :
  original_gamma:(string, Type.t) Hashtbl.t ->
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.t -> Expr.Set.t option

val check_entailment :
  ?matching:bool ->
  Utils.Containers.SS.t ->
  PFS.t ->
  Gil_syntax.Expr.t list ->
  Type_env.t ->
  bool

(** [is_equal e1 e2 pfs gamma] checks whether or not << pfs, gamma |- e1 = e2
    >>. *)
val is_equal :
  ?matching:bool ->
  pfs:PFS.t ->
  gamma:Type_env.t ->
  Gil_syntax.Expr.t ->
  Gil_syntax.Expr.t ->
  bool

(** [is_different e1 e2 pfs gamma] checks whether or not << pfs, gamma |- e1 <>
    e2 >>. *)
val is_different :
  pfs:PFS.t ->
  gamma:Type_env.t ->
  Gil_syntax.Expr.t ->
  Gil_syntax.Expr.t ->
  bool

val num_is_less_or_equal :
  pfs:PFS.t ->
  gamma:Type_env.t ->
  Gil_syntax.Expr.t ->
  Gil_syntax.Expr.t ->
  bool

val resolve_loc_name :
  pfs:PFS.t -> gamma:Type_env.t -> Gil_syntax.Expr.t -> string option
