open Gil_syntax
module Utf16 : module type of Utf16_encoding

exception SMT_unknown
exception SMT_error of string

(** Terminal-only, serial shutdown of the current solver. On success the owned
    process has been closed and reaped by Simple_smt.stop. A repeated successful
    call is a no-op; a failed close is remembered and re-raised. The original
    solver record stays strongly rooted to prevent its GC finalizer closing it
    again. Solver I/O and reinitialization are rejected after shutdown begins.
    This is not a reset or an old-generation recovery cleanup API. *)
val shutdown_solver : unit -> unit

(** Diagnostic provenance only, active iff GILLIAN_NATIVE_SMT_CONTEXT_DIR is set.
    Original operation arguments are materialized before [f], scoped through
    nested solver calls, and restored on normal or exceptional exit. With the
    environment unset, [make_context] is never called. No formulas/policy change. *)
val with_native_smt_context :
  (unit -> Yojson.Safe.t) -> (unit -> 'a) -> 'a

(** Native model together with its originating datatype declarations, retained
    across solver resets and cache hits. *)
type model

(** Requested optional query timeout, as a millisecond option string: the
    smaller of [cap] and the configured SMT limit, with configured zero leaving
    [cap] unchanged. This read-only policy value is not a host wallclock timer
    or proof authority. *)
val optional_timeout : int -> string

(** Read-only formatter for the complete existing SMT type environment. *)
val pp_typenv : (string, Type.t) Hashtbl.t Fmt.t

(** The existing ordinary plain PRIMARY command, exposed for source-coupled
    diagnostic checks. Reading or rendering it neither executes a query nor
    changes the solver policy or any JavaScript-facing API. *)
val primary_check_command : Sexplib.Sexp.t
val primary_check_command_text : Sexplib.Sexp.t -> string

(** Read-only structural guard for the retained trace-index witness shape.
    [Some query] is the whole original FS plus one positive1 candidate equality,
    using the same original Number expression and all existing Gamma entries.
    [None] means the guard declines (including an already-present candidate).
    No facts/types/aliases are invented in the original state. This constructs
    a search candidate; it does not establish SAT, UNSAT or a proof. *)
val positive_trace_index_witness_query :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.Set.t option

(** One optional native attempt on that complete strengthened query, requesting
    [optional_timeout 1000] with phase selection 3. This option is not a separate
    protocol wallclock timer. Only actual validated SAT returns [Some model].
    [None] also covers
    guard decline, strengthened-query UNSAT and UNKNOWN; it proves nothing
    about UNSAT of the original FS. Other solver/model errors propagate. The
    original FS/Gamma and required fallback/error/cache policies are unchanged;
    no result is published under a candidate cache key by this helper. *)
val positive_trace_index_model :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> model option

(** Optional complete-query index witness. Only validated native SAT returns a
    model; declined, UNSAT or UNKNOWN guesses retain the required fallback.
    This helper neither changes the caller FS/Gamma nor populates its cache. *)
val formatted_index_model :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> model option

(** One finite-literal bit candidate for an already-compared, typed Number
    used by a formatter. The entire original FS and Gamma remain; the added
    ValueEqual is a search hint, not a consequence (especially for signed zero).
    Declines ambiguity and existing literal bit pins. *)
val literal_formatter_witness_query :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> Expr.Set.t option

(** One optional native complete-query attempt. Only validated SAT succeeds;
    UNSAT/UNKNOWN/decline prove nothing about the original query. No cache or
    caller state is changed; other solver/model errors still propagate. *)
val literal_formatter_model :
  Expr.Set.t -> (string, Type.t) Hashtbl.t -> model option

(** Native Z3 phase policy controls search order only. Default 3 matches Z3; an
    explicit override is useful for exact solver-defect reproductions. *)
val exec_sat :
  ?caller_kind:string ->
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
(* Caller labels are diagnostic only; native formulas, policies and caches
   are independent of them. Native result logs join the actual dump filename. *)
val proves_unsat : ?caller_kind:string -> Expr.Set.t -> (string, Type.t) Hashtbl.t -> bool

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
