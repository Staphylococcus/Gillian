open Gil_syntax
open Utils
open Simple_smt
open Syntaxes.Option
open Prog_env

(* open Ctx *)
module L = Logging
module Utf16 = Utf16_encoding

let smt_cost_profile_id = ref 0

let smt_cost_profile caller =
  if Sys.getenv_opt "GILLIAN_SMT_COST_PROFILE" <> Some "1" then
    fun _ _ -> ()
  else (
    incr smt_cost_profile_id;
    let id = !smt_cost_profile_id in
    fun phase query ->
      let wall = Unix.gettimeofday () in
      let cpu = Sys.time () in
      L.normal (fun m ->
          m "SMT_COST id=%d phase=%s query=%s caller=%s wall=%.9f cpu=%.9f"
            id phase query caller wall cpu))

exception SMT_error of string

let exceptf fmt = Fmt.kstr (fun s -> raise (SMT_error s)) fmt

let z3_config =
  [
    ("model", "true");
    (* Reject a solver-produced witness that violates the submitted formula.
       Mixed sequence-length/FP conversions can otherwise return invalid SAT
       models. The protocol heartbeat propagates the validation error. *)
    ("model_validate", "true");
    ("proof", "false");
    ("unsat_core", "false");
    ("auto_config", "true");
    ("timeout", try Sys.getenv "SMT_TIMEOUT" with Not_found -> "30000");
  ]

let () = Sys.(set_signal sigpipe Signal_ignore)

exception SMT_unknown

(* A model outlives the solver context that produced it, including through the
   SAT cache. Keep the actual datatype commands, not dynamic declaration
   builders whose user-datatype set can change on the next query. *)
type model = { values : sexp; sort_declarations : sexp list }

let pp_sexp = Sexplib.Sexp.pp_hum
let pp_model fmt model = pp_sexp fmt model.values
let ( <| ) constr e = app constr [ e ]
let ( $$ ) constr l = app constr l

(* GIL Num is IEEE-754 binary64, not an SMT mathematical real. *)
let t_number : sexp =
  List [ atom "_"; atom "FloatingPoint"; atom "11"; atom "53" ]

let to_number args =
  app (List [ atom "_"; atom "to_fp"; atom "11"; atom "53" ]) args

let rne = atom "RNE"

let number_literal n =
  to_number [ atom (Printf.sprintf "#x%016Lx" (Int64.bits_of_float n)) ]

let fp_un op a = app_ op [ a ]
let fp_bin op a b = app_ op [ a; b ]
let fp_arith op a b = app_ op [ rne; a; b ]

(* CExprEval uses Zarith division/remainder, which truncate toward zero.
   SMT integer div/mod use Euclidean semantics. Zero-divisor executions are
   rejected by the total-mode domain checks; logical zero terms stay arbitrary. *)
let integer_quotient a b =
  let zero = int_k 0 in
  let negative x = num_lt x zero in
  let absolute x = ite (negative x) (num_neg x) x in
  let magnitude = num_div (absolute a) (absolute b) in
  ite (bool_not (eq (negative a) (negative b))) (num_neg magnitude) magnitude

let fp_finite a =
  bool_not (bool_or (fp_un "fp.isNaN" a) (fp_un "fp.isInfinite" a))

(* Truncate, then wrap modulo 2^width. Binary64 values of magnitude at least
   2^(width+52) are multiples of 2^width. Smaller magnitudes fit the native
   unsigned conversion of that width+52; sanitize its domain before applying
   it. This also maps NaN/infinities and both zeros to positive zero. *)
let integer_wrap_bits ~width value =
  let wide = width + 52 in
  let absolute = fp_un "fp.abs" value in
  let safe =
    ite
      (fp_bin "fp.lt" absolute (number_literal (Float.ldexp 1. wide)))
      absolute (number_literal 0.)
  in
  let whole =
    app
      (List [ atom "_"; atom "fp.to_ubv"; atom (string_of_int wide) ])
      [ atom "RTZ"; safe ]
  in
  let low =
    app
      (List
         [
           atom "_"; atom "extract"; atom (string_of_int (width - 1)); atom "0";
         ])
      [ whole ]
  in
  ite (fp_un "fp.isNegative" value) (app_ "bvneg" [ low ]) low

let integer_wrap ~width ~signed value =
  let wrapped = integer_wrap_bits ~width value in
  let conversion = if signed then "to_fp" else "to_fp_unsigned" in
  let modular =
    app
      (List [ atom "_"; atom conversion; atom "11"; atom "53" ])
      [ rne; wrapped ]
  in
  (* The nonnegative in-range case is ordinary IEEE truncation. Exposing it
     avoids an 84-bit conversion proof for each native array index. *)
  let in_range =
    bool_and
      (fp_bin "fp.leq" (number_literal 0.) value)
      (fp_bin "fp.lt" value
         (number_literal (Float.ldexp 1. (if signed then width - 1 else width))))
  in
  let truncated = app_ "fp.roundToIntegral" [ atom "RTZ"; value ] in
  ite in_range
    (ite (fp_un "fp.isZero" truncated) (number_literal 0.) truncated)
    modular

(* Exact truncation on finite binary64 values. Partial source operators must
   establish their domain through Totality before using this SMT extension. *)
let number_to_integer value =
  let small =
    bool_and
      (fp_bin "fp.leq" (number_literal 0.) value)
      (fp_bin "fp.lt" value (number_literal 65536.))
  in
  (* In this guarded interval unsigned 16-bit RTZ conversion is exact. The
     fallback retains every other finite Number; this is not an input bound. *)
  ite small
    (app_ "bv2int"
       [
         app
           (List [ atom "_"; atom "fp.to_ubv"; atom "16" ])
           [ atom "RTZ"; value ];
       ])
    (real_to_int
       (fp_un "fp.to_real" (app_ "fp.roundToIntegral" [ atom "RTZ"; value ])))

(* Explicit integer counts may span the whole Array index range. Keep the
   existing small conversion and UTF-16 indexing encoder unchanged; above that
   interval unsigned 32-bit RTZ remains exact. Every other finite Number uses
   the original general conversion. This selects an encoding, not input scope. *)
let number_to_integer_count value =
  let wide = bool_and
      (fp_bin "fp.leq" (number_literal 65536.) value)
      (fp_bin "fp.lt" value (number_literal 4294967296.)) in
  ite wide
    (app_ "bv2int"
      [app (List [ atom "_"; atom "fp.to_ubv"; atom "32" ])
         [ atom "RTZ"; value ]])
    (number_to_integer value)

module Variant = struct
  module type S = sig
    val name : string
    val params : (string * sexp) list
    val recognizer : string
    val recognize : sexp -> sexp
  end

  module type Nullary = sig
    include S

    val construct : sexp
  end

  module type Unary = sig
    include S

    val construct : sexp -> sexp
    val access : sexp -> sexp
  end

  module type Nary = sig
    include S

    (* val num_params : int *)
    val construct : sexp list -> sexp
  end

  let nul ?recognizer name =
    let recognizer = Option.value recognizer ~default:("is" ^ name) in
    let module M = struct
      let name = name
      let params = []
      let construct = atom name $$ []
      let recognizer = recognizer
      let recognize x = atom recognizer <| x
    end in
    (module M : Nullary)

  let un ?recognizer name param param_typ =
    let module N = (val nul ?recognizer name : Nullary) in
    let module M = struct
      include N

      let params = [ (param, param_typ) ]
      let construct x = atom name <| x
      let accessor = atom param
      let access x = accessor <| x
    end in
    (module M : Unary)

  let n ?recognizer name param_typs =
    let module N = (val nul ?recognizer name : Nullary) in
    let module M = struct
      include N

      let params =
        List.mapi
          (fun i param_typ -> ("param-" ^ string_of_int i, param_typ))
          param_typs

      let num_params = List.length params

      let construct xs =
        let num_params_provided = List.length xs in
        if num_params_provided == num_params then atom name $$ xs
        else
          let msg =
            Printf.sprintf
              "Invalid number of parameters for the constructor %s. %d \
               parameters were provided, but %d were expected."
              name num_params_provided num_params
          in
          raise (Failure msg)
    end in
    (module M : Nary)
end

(** {2 Tracking the declarations a query depends on}

    The solver is reset before every query (see [reset_solver]), so each query
    must (re-)send the datatype and function declarations it relies on. At
    encoding time, we keep track of the necessary dependencies of the assertion
    being encoded through [Require_definition]. *)

type definition = {
  id : int;
  decls : unit -> sexp list;  (** the SMT commands declaring this definition *)
  depends_on : definition list;  (** definitions that must be emitted first *)
}

let make_definition' =
  let counter = ref 0 in
  fun ?(depends_on = []) decls ->
    incr counter;
    { id = !counter; decls; depends_on }

let make_definition ?depends_on decls =
  let decls () = decls in
  make_definition' ?depends_on decls

type _ Effect.t +=
  | Require_definition : definition -> unit Effect.t
  | Require_usr_datatypes : SS.t -> unit Effect.t
  | Get_usr_datatypes :
      ((module Variant.S) * (string * string list * (module Variant.S) list))
      list
      Effect.t

let require_definition d = Effect.perform (Require_definition d)
let require_usr_datatypes ds = Effect.perform (Require_usr_datatypes ds)
let get_usr_datatypes () = Effect.perform Get_usr_datatypes

let datatype_cache :
    ( string,
      SS.t
      * (module Variant.Unary)
      * (string * string list * (module Variant.S) list) )
    Hashtbl.t =
  Hashtbl.create Config.medium_tbl_size

let constructor_cache : (string, SS.t * (module Variant.Nary)) Hashtbl.t =
  Hashtbl.create Config.medium_tbl_size

let with_necessary_usr_datatypes (f : unit -> 'a) : 'a =
  let needed_usr_datatypes = ref SS.empty in
  match f () with
  | x -> x
  | effect Require_usr_datatypes ds, k ->
      needed_usr_datatypes := SS.union !needed_usr_datatypes ds;
      Effect.Deep.continue k ()
  | effect Get_usr_datatypes, k ->
      let datatypes =
        SS.fold
          (fun name acc ->
            let _, (module V : Variant.Unary), dt =
              Hashtbl.find datatype_cache name
            in
            ((module V : Variant.S), dt) :: acc)
          !needed_usr_datatypes []
      in
      Effect.Deep.continue k datatypes

(** Run [f], returning its result together with the set of definitions it
    required (keyed by id), closed under the [depends_on] relation. *)
let with_necessary_definitions (f : unit -> 'a) :
    'a * (int, definition) Hashtbl.t =
  let needed_defs = Hashtbl.create 17 in
  let rec add_def d =
    if not (Hashtbl.mem needed_defs d.id) then (
      Hashtbl.replace needed_defs d.id d;
      List.iter add_def d.depends_on)
  in
  let result =
    match f () with
    | x -> x
    | effect Require_definition d, k ->
        add_def d;
        Effect.Deep.continue k ()
  in
  (result, needed_defs)

(** Send each required definition through [emit], preceded by the definitions it
    depends on (so declarations always come before their uses). *)
let emit_definitions ~emit (needed : (int, definition) Hashtbl.t) =
  let emitted = Hashtbl.create (Hashtbl.length needed) in
  let rec go d =
    if not (Hashtbl.mem emitted d.id) then (
      Hashtbl.replace emitted d.id ();
      List.iter go d.depends_on;
      List.iter emit (d.decls ()))
  in
  Hashtbl.iter (fun _ d -> go d) needed

let solver =
  ref
    {
      command = (fun _ -> failwith "Uninitialized solver");
      stop = (fun () -> failwith "Uninitialized solver");
      force_stop = (fun () -> failwith "Uninitialized solver");
      config = z3;
      raw_command = (fun _ -> failwith "Uninitialized solver");
    }

(* Terminal cleanup owns the original record, not just its protected copy.
   Keep this strong root after close: Simple_smt's non-idempotent GC finalizer
   belongs to that original record. Pre-shutdown recovery is unchanged; retired
   generations are not explicitly closed by this terminal-only interface. *)
type terminal_shutdown_state =
  | Terminal_open
  | Terminal_closing
  | Terminal_closed
  | Terminal_failed of exn * Printexc.raw_backtrace

let terminal_shutdown_state = ref Terminal_open
let terminal_solver_owner : Simple_smt.solver option ref = ref None

let ensure_solver_open () =
  match !terminal_shutdown_state with
  | Terminal_open -> ()
  | Terminal_closing | Terminal_closed | Terminal_failed _ ->
      raise (SMT_error "SMT solver is terminally shut down")

let shutdown_solver () =
  match !terminal_shutdown_state with
  | Terminal_closed -> ()
  | Terminal_closing ->
      raise (SMT_error "SMT terminal shutdown is already in progress")
  | Terminal_failed (error, backtrace) ->
      Printexc.raise_with_backtrace error backtrace
  | Terminal_open ->
      terminal_shutdown_state := Terminal_closing;
      (try
         (match !terminal_solver_owner with
         | None -> ()
         | Some original -> original.stop ());
         terminal_shutdown_state := Terminal_closed
       with error ->
         let backtrace = Printexc.get_raw_backtrace () in
         terminal_shutdown_state := Terminal_failed (error, backtrace);
         Printexc.raise_with_backtrace error backtrace)

(* One ordinary plain full-request check. Keep the dependency's exact typed
   reply grammar and protected command/heartbeat; model_eval' is also plain. *)
let primary_check_command : sexp =
  list [ atom "check-sat" ]

(* Phase zero is an explicit caller policy, not a formula or test-name match. *)
let phase_zero_primary_check_command : sexp =
  Sexplib.Sexp.of_string
    "(check-sat-using(or-else(try-for(then simplify solve-eqs smt fail-if-undecided)1000)(then simplify solve-eqs fpa2bv smt)))"

let primary_check_command_for_phase phase_selection =
  if phase_selection = 0 then phase_zero_primary_check_command
  else primary_check_command

let primary_check_command_text command = Sexplib.Sexp.to_string_mach command

let primary_check (solver : Simple_smt.solver) command : Simple_smt.result =
  match solver.command command with
  | Sexplib.Sexp.Atom "unsat" -> Unsat
  | Sexplib.Sexp.Atom "sat" -> Sat
  | Sexplib.Sexp.Atom "unknown" -> Unknown
  | answer -> raise (UnexpectedSolverResponse answer)

let cmd s = ack_command !solver s
let reset = list [ atom "reset" ]

let rec init_solver () =
  let () = ensure_solver_open () in
  let z3 = new_solver z3 in
  let () = terminal_solver_owner := Some z3 in
  let command = protected_command z3 in
  let () = solver := { z3 with command } in
  (* Configuration *)
  let () =
    z3_config |> List.iter (fun (k, v) -> cmd (set_option (":" ^ k) v))
  in
  ()

and protected_command solver s =
  let () = ensure_solver_open () in
  let open Sexplib in
  let open Gillian_result.Exc in
  let res =
    try
      let r = solver.command s in
      (* Perform a "heartbeat" after each command so we know ASAP if the solver died *)
      match solver.raw_command "(echo \"gillian\")" with
      | Sexp.Atom "gillian" -> Ok r
      | s -> Fmt.error "SMT heartbeat gave unexpected result: %a" Sexp.pp_hum s
    with Sys_error s -> Fmt.error "Error when calling SMT solver: %s" s
  in
  match res with
  | Ok r -> r
  | Error msg ->
      Logging.normal (fun m -> m "%s" msg);
      init_solver ();
      raise (internal_error msg)

let sanitize_identifier =
  let pattern = Str.regexp "#" in
  Str.global_replace pattern "$$"

let is_true = function
  | Sexplib.Sexp.Atom "true" -> true
  | _ -> false

type typenv = (string, Type.t) Hashtbl.t [@@deriving to_yojson]

let fs_to_yojson fs = fs |> Expr.Set.to_list |> list_to_yojson Expr.to_yojson

let sexps_to_yojson sexps =
  `List (List.map (fun sexp -> `String (Sexplib.Sexp.to_string_mach sexp)) sexps)

let pp_typenv = Fmt.(Dump.hashtbl string (Fmt.of_to_string Type.str))

(* Polymorphic equality merges +0 and -0. Cache keys must use structural
   expression identity, since division can distinguish their signs. *)
module Formula_cache = Hashtbl.Make (struct
  type t = Expr.Set.t * (string * Type.t) list

  let equal (a, ga) (b, gb) = Expr.Set.equal a b && ga = gb
  let hash (fs, gamma) = Hashtbl.hash (Expr.Set.elements fs, gamma)
end)

let encoding_cache = Formula_cache.create Config.big_tbl_size
let sat_cache = Formula_cache.create Config.big_tbl_size

(* A timed-out sufficient precheck proved nothing. Remember only that this
   optional attempt was inconclusive; never consult this table for a required
   satisfiability query. A later actual SAT/UNSAT cache entry takes precedence. *)
let inconclusive_prechecks = Formula_cache.create Config.big_tbl_size

let formula_key fs gamma =
  (fs, Hashtbl.to_seq gamma |> List.of_seq |> List.sort Stdlib.compare)

let declare_const const typ = atom "declare-const" $$ [ atom const; typ ]

let quant q (vars : (sexp * sexp) list) (s : sexp) : sexp =
  let vars = vars |> List.map (fun (v, t) -> list [ v; t ]) in
  app (atom q) [ list vars; s ]

let forall' = quant "forall"

let forall (vars : (string * sexp) list) (s : sexp) : sexp =
  let vars =
    vars |> List.map (fun (v, t) -> (atom (sanitize_identifier v), t))
  in
  forall' vars s

let exists' = quant "exists"

let exists (vars : (string * sexp) list) (s : sexp) : sexp =
  let vars =
    vars |> List.map (fun (v, t) -> (atom (sanitize_identifier v), t))
  in
  exists' vars s

let t_seq t = list [ atom "Seq"; t ]

(* GIL strings are byte strings. A native sequence preserves their contents
   without imposing a UTF-16 interpretation on generic GIL operations. *)
let t_byte : sexp = List [ atom "_"; atom "BitVec"; atom "8" ]
let t_bytes = t_seq t_byte
let seq_len s = atom "seq.len" <| s
let seq_extract s offset length = atom "seq.extract" $$ [ s; offset; length ]
let seq_nth s offset = atom "seq.nth" $$ [ s; offset ]
let seq_concat ss = atom "seq.++" $$ ss
let seq_unit s = atom "seq.unit" <| s

let set_union' ext xs =
  let f =
    match ext with
    | CVC5 -> atom "set.union"
    | _ -> atom "union"
  in
  f $$ xs

let set_intersection' ext xs =
  let f =
    match ext with
    | CVC5 -> atom "set.inter"
    | _ -> atom "intersection"
  in
  f $$ xs

let declare_recognizer ~name ~constructor ~typ =
  define_fun name
    [ ("x", typ) ]
    t_bool
    (list [ atom "_"; atom "is"; atom constructor ] <| atom "x")

let mk_datatype' (name, type_params, (variants : (module Variant.S) list)) =
  let constructors, recognizer_defs =
    variants
    |> List.map (fun v ->
           let module V = (val v : Variant.S) in
           let constructor = (V.name, V.params) in
           let recognizer_def =
             declare_recognizer ~name:V.recognizer ~constructor:V.name
               ~typ:(atom name)
           in
           (constructor, recognizer_def))
    |> List.split
  in
  let datatype = (name, type_params, constructors) in
  (atom name, datatype, recognizer_defs)

(* Builds a datatype declaration together with its recognizers, and returns
   both the type's atom and a {!definition} that can be required during
   encoding. [depends_on] lists the datatypes this one refers to in its fields,
   which must therefore be declared first. *)
let mk_datatype
    ?depends_on
    name
    type_params
    (variants : (module Variant.S) list) =
  let name', (_, _, constructors), recognizer_defs =
    mk_datatype' (name, type_params, variants)
  in
  let decl = declare_datatype name type_params constructors in
  (name', make_definition ?depends_on (decl :: recognizer_defs))

(* Builds a definition for mutually recursive datatypes that are evaluated dynamically on each use.
   We use this for user datatypes, which must be mutually recursive with GIL literals *)
let mk_datatypes_dyn
    ?depends_on
    (get : unit -> (string * string list * (module Variant.S) list) list) =
  let mk () =
    let _, datatypes, recognizer_defs =
      get () |> List.map mk_datatype' |> List_utils.split3
    in
    let decl = declare_datatypes datatypes in
    decl :: List.concat recognizer_defs
  in
  make_definition' ?depends_on mk

let mk_fun_decl ?depends_on name param_types result_type =
  let decl = declare_fun name param_types result_type in
  (atom name, make_definition ?depends_on [ decl ])

module Type_operations = struct
  open Variant
  module Undefined = (val nul "UndefinedType" : Nullary)
  module Null = (val nul "NullType" : Nullary)
  module Empty = (val nul "EmptyType" : Nullary)
  module None = (val nul "NoneType" : Nullary)
  module Boolean = (val nul "BooleanType" : Nullary)
  module Int = (val nul "IntType" : Nullary)
  module Number = (val nul "NumberType" : Nullary)
  module String = (val nul "StringType" : Nullary)
  module Utf16String = (val nul "Utf16Type" : Nullary)
  module Object = (val nul "ObjectType" : Nullary)
  module List = (val nul "ListType" : Nullary)
  module Type = (val nul "TypeType" : Nullary)
  module Set = (val nul "SetType" : Nullary)
  module Datatype = (val un "DatatypeType" "datatype-id" t_int)

  let t_gil_type, def_gil_type =
    mk_datatype "GIL_Type" []
      [
        (module Undefined : Variant.S);
        (module Null : Variant.S);
        (module Empty : Variant.S);
        (module None : Variant.S);
        (module Boolean : Variant.S);
        (module Int : Variant.S);
        (module Number : Variant.S);
        (module String : Variant.S);
        (module Utf16String : Variant.S);
        (module Object : Variant.S);
        (module List : Variant.S);
        (module Type : Variant.S);
        (module Set : Variant.S);
        (module Datatype : Variant.S);
      ]
end

let t_gil_type = Type_operations.t_gil_type
let def_gil_type = Type_operations.def_gil_type

module Lit_operations = struct
  open Variant

  let gil_literal_name = "GIL_Literal"
  let t_gil_literal = atom gil_literal_name

  module Undefined = (val nul "Undefined" : Nullary)
  module Null = (val nul "Null" : Nullary)
  module Empty = (val nul "Empty" : Nullary)
  module Bool = (val un "Bool" "bValue" t_bool : Unary)
  module Int = (val un "Int" "iValue" t_int : Unary)
  module Num = (val un "Num" "nValue" t_number : Unary)
  module String = (val un "String" "sValue" t_bytes : Unary)
  module Utf16String = (val un "Utf16String" "u16Value" Utf16.sort : Unary)
  module Loc = (val un "Loc" "locValue" t_int : Unary)
  module Type = (val un "Type" "tValue" t_gil_type : Unary)
  module List = (val un "List" "listValue" (t_seq t_gil_literal) : Unary)
  module None = (val nul "None" : Nullary)

  let gil_literal_variants =
    [
      (module Undefined : Variant.S);
      (module Null : Variant.S);
      (module Empty : Variant.S);
      (module Bool : Variant.S);
      (module Int : Variant.S);
      (module Num : Variant.S);
      (module String : Variant.S);
      (module Utf16String : Variant.S);
      (module Loc : Variant.S);
      (module Type : Variant.S);
      (module List : Variant.S);
      (module None : Variant.S);
    ]

  let gil_literal_datatypes () =
    let usr_datatype_lit_variants, usr_datatypes =
      Stdlib.List.split (get_usr_datatypes ())
    in
    (gil_literal_name, [], gil_literal_variants @ usr_datatype_lit_variants)
    :: usr_datatypes

  let def_gil_literal =
    mk_datatypes_dyn ~depends_on:[ def_gil_type ] gil_literal_datatypes
end

let t_gil_literal = Lit_operations.t_gil_literal
let def_gil_literal = Lit_operations.def_gil_literal
let t_gil_literal_list = t_seq t_gil_literal
let t_gil_literal_set = t_set t_gil_literal

let native_sort_of_type =
  let open Type in
  function
  | IntType | ObjectType -> t_int
  | StringType -> t_bytes
  | Utf16Type -> Utf16.sort
  | ListType ->
      require_definition def_gil_literal;
      t_gil_literal_list
  | BooleanType -> t_bool
  | NumberType -> t_number
  | UndefinedType | NoneType | EmptyType | NullType ->
      require_definition def_gil_literal;
      t_gil_literal
  | SetType ->
      require_definition def_gil_literal;
      t_gil_literal_set
  | TypeType ->
      require_definition def_gil_type;
      t_gil_type
  | DatatypeType name -> atom name

module Datatype_operations = struct
  let user_def_datatype_lit_variant_name (datatype_name : string) =
    "Datatype" ^ datatype_name

  let user_def_datatype_lit_param_name (datatype_name : string) =
    datatype_name ^ "Value"

  let mk_user_def_datatype_lit_variant Datatype.{ datatype_name; _ } =
    let variant_name = user_def_datatype_lit_variant_name datatype_name in
    let t_datatype = atom datatype_name in
    let parameter_name = user_def_datatype_lit_param_name datatype_name in
    Variant.un variant_name parameter_name t_datatype

  let rec encode_single_constructor ~cycle (c : Constructor.t) =
    let param_types =
      c.constructor_fields
      |> List.map @@ function
         | Some t ->
             let () =
               match t with
               | Type.DatatypeType name -> ensure_encoded name
               | _ -> ()
             in
             native_sort_of_type t
         | None -> t_gil_literal
    in
    let variant = Variant.n c.constructor_name param_types in
    Hashtbl.replace constructor_cache c.constructor_name (cycle, variant);
    (module (val variant : Variant.Nary) : Variant.S)

  and encode_single_datatype ~cycle name =
    let d = Datatype_env.get_datatype_exn name in
    let ctor_variants =
      List.map (encode_single_constructor ~cycle) d.datatype_constructors
    in
    let datatype = (name, [], ctor_variants) in
    let lit_variant = mk_user_def_datatype_lit_variant d in
    Hashtbl.replace datatype_cache name (cycle, lit_variant, datatype)

  and ensure_encoded name : unit =
    if not (Hashtbl.mem datatype_cache name) then
      let cycle = SS.add name (Datatype_env.get_datatype_cycle name) in
      SS.iter (encode_single_datatype ~cycle) cycle

  let ensure_encoded_c cname : unit =
    let c = Datatype_env.get_constructor_exn cname in
    ensure_encoded c.constructor_datatype

  let encode_datatype name =
    ensure_encoded name;
    let cycle, lit_variant, _ = Hashtbl.find datatype_cache name in
    require_usr_datatypes cycle;
    lit_variant

  let encode_constructor cname =
    ensure_encoded_c cname;
    let cycle, variant = Hashtbl.find constructor_cache cname in
    require_usr_datatypes cycle;
    variant
end

let seq_of ~typ xs =
  require_definition def_gil_literal;
  match xs with
  | [] -> as_type (atom "seq.empty") typ
  | xs -> xs |> List.map seq_unit |> seq_concat

let set_of xs =
  require_definition def_gil_literal;
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> aux (set_insert Z3 x acc) xs
  in
  aux (set_empty Z3 t_gil_literal) xs

module Ext_lit_operations = struct
  open Variant

  module Gil_sing_elem =
    (val un "Elem" ~recognizer:"isSingular" "singElem" t_gil_literal : Unary)

  module Gil_set = (val un "Set" "setElem" t_gil_literal_set : Unary)

  let t_gil_ext_literal, def_gil_ext_literal =
    mk_datatype ~depends_on:[ def_gil_literal ] "Extended_GIL_Literal" []
      [ (module Gil_sing_elem : Variant.S); (module Gil_set : Variant.S) ]
end

module Axiomatised_operations = struct
  let slen, def_slen = mk_fun_decl "s-len" [ t_bytes ] t_number

  let llen, def_llen =
    mk_fun_decl ~depends_on:[ def_gil_literal ] "l-len" [ t_gil_literal_list ]
      t_int

  let num2str, def_num2str = mk_fun_decl "num2str" [ t_number ] t_bytes
  let str2num, def_str2num = mk_fun_decl "str2num" [ t_bytes ] t_number
  let num2utf16, def_num2utf16 = mk_fun_decl "num2utf16" [ t_number ] Utf16.sort
  let utf162num, def_utf162num = mk_fun_decl "utf162num" [ Utf16.sort ] t_number
  let snth, def_snth = mk_fun_decl "s-nth" [ t_bytes; t_number ] t_bytes

  let lrev, def_lrev =
    mk_fun_decl ~depends_on:[ def_gil_literal ] "l-rev" [ t_gil_literal_list ]
      t_gil_literal_list
end

let t_gil_ext_literal = Ext_lit_operations.t_gil_ext_literal
let def_gil_ext_literal = Ext_lit_operations.def_gil_ext_literal
let str_codes = Hashtbl.create 1000
let str_counter = ref 0

(* Location and user-datatype identities remain opaque, distinct codes. *)
let encode_symbol s =
  match Hashtbl.find_opt str_codes s with
  | Some code -> int_k code
  | None ->
      let code = int_k !str_counter in
      let () = Hashtbl.add str_codes s !str_counter in
      let () = incr str_counter in
      code

let encode_string s =
  if String.length s = 0 then as_type (atom "seq.empty") t_bytes
  else
    String.to_seq s |> List.of_seq
    |> List.map (fun byte ->
           seq_unit (atom (Printf.sprintf "#x%02x" (Char.code byte))))
    |> seq_concat

let encode_type (t : Type.t) =
  require_definition def_gil_type;
  try
    match t with
    | UndefinedType -> Type_operations.Undefined.construct
    | NullType -> Type_operations.Null.construct
    | EmptyType -> Type_operations.Empty.construct
    | NoneType -> Type_operations.None.construct
    | BooleanType -> Type_operations.Boolean.construct
    | IntType -> Type_operations.Int.construct
    | NumberType -> Type_operations.Number.construct
    | StringType -> Type_operations.String.construct
    | Utf16Type -> Type_operations.Utf16String.construct
    | ObjectType -> Type_operations.Object.construct
    | ListType -> Type_operations.List.construct
    | TypeType -> Type_operations.Type.construct
    | SetType -> Type_operations.Set.construct
    | DatatypeType name ->
        name |> encode_symbol |> Type_operations.Datatype.construct
  with _ -> exceptf "DEATH: encode_type with arg: %a" Type.pp t

module Encoding = struct
  type kind =
    | Native of Type.t
        (** This value encodes to an SMTLIB native type, like Int or Seq *)
    | Simple_wrapped  (** Cannot be a set *)
    | Extended_wrapped  (** Can be a set *)

  type t = {
    consts : (string * sexp) Hashset.t; [@default Hashset.empty ()]
    kind : kind;
    extra_asrts : sexp list;
    facts : sexp list;
        (** Intrinsic primitive facts, separate from expression domain guards.
        *)
    expr : sexp; [@main]
  }
  [@@deriving make]

  let merge_consts a b =
    let result = Hashset.copy a in
    let () = b |> Hashset.iter (Hashset.add result) in
    result

  let all_consts encs =
    List.fold_left
      (fun acc enc -> merge_consts acc enc.consts)
      (Hashset.empty ()) encs

  let undefined_encoding =
    make ~kind:Simple_wrapped Lit_operations.Undefined.construct

  let null_encoding = make ~kind:Simple_wrapped Lit_operations.Null.construct
  let empty_encoding = make ~kind:Simple_wrapped Lit_operations.Empty.construct
  let none_encoding = make ~kind:Simple_wrapped Lit_operations.None.construct
  let native typ = make ~kind:(Native typ)

  let make_const ?extra_asrts ~typ kind const =
    let const = sanitize_identifier const in
    let consts = Hashtbl.singleton (const, typ) () in
    make ?extra_asrts ~consts ~kind (atom const)

  let native_const ?extra_asrts typ =
    make_const ?extra_asrts ~typ:(native_sort_of_type typ) (Native typ)

  let ( >- ) expr typ = native typ expr

  let ( let>- ) (enc : t) (f : t -> t) =
    let enc' = f enc in
    let consts = merge_consts enc.consts enc'.consts in
    let extra_asrts = enc.extra_asrts @ enc'.extra_asrts in
    let facts = enc.facts @ enc'.facts in
    { enc' with consts; extra_asrts; facts }

  let ( let>-- ) (encs : t list) (f : t list -> t) =
    let enc' = f encs in
    let consts = merge_consts (all_consts encs) enc'.consts in
    let extra_asrts =
      List.concat_map (fun e -> e.extra_asrts) encs @ enc'.extra_asrts
    in
    let facts = List.concat_map (fun e -> e.facts) encs @ enc'.facts in
    { enc' with consts; extra_asrts; facts }

  let get_native
      ~accessor
      ~recognizer
      ~typ
      ({ expr; kind; extra_asrts; _ } as enc) : t =
    let expr, guards =
      match kind with
      | Native _ ->
          (* No additional check is performed on native type,
           it should be already type checked *)
          (expr, [])
      | Simple_wrapped ->
          require_definition def_gil_literal;
          (accessor expr, [ recognizer expr ])
      | Extended_wrapped ->
          require_definition def_gil_ext_literal;
          let simply_wrapped = Ext_lit_operations.Gil_sing_elem.access expr in
          ( accessor simply_wrapped,
            [
              recognizer simply_wrapped;
              Ext_lit_operations.Gil_sing_elem.recognize expr;
            ] )
    in
    let extra_asrts = guards @ extra_asrts in
    let kind = Native typ in
    { enc with expr; extra_asrts; kind }

  let simply_wrapped expr =
    require_definition def_gil_literal;
    make ~kind:Simple_wrapped expr

  let extended_wrapped expr =
    require_definition def_gil_ext_literal;
    make ~kind:Extended_wrapped expr

  (** Takes a value either natively encoded or simply wrapped and returns a
      value simply wrapped. Careful: do not use wrap with a a set, as they
      cannot be simply wrapped *)
  let simple_wrap ({ expr; kind; extra_asrts; _ } as enc) =
    let open Lit_operations in
    require_definition def_gil_literal;
    match kind with
    | Simple_wrapped -> enc
    | Native typ ->
        let construct =
          match typ with
          | IntType -> Int.construct
          | NumberType -> Num.construct
          | StringType -> String.construct
          | Utf16Type -> Utf16String.construct
          | ObjectType -> Loc.construct
          | TypeType -> Type.construct
          | BooleanType -> Bool.construct
          | ListType -> List.construct
          | DatatypeType name ->
              let (module U : Variant.Unary) =
                Datatype_operations.encode_datatype name
              in
              U.construct
          | UndefinedType | NullType | EmptyType | NoneType | SetType ->
              exceptf "Cannot simple-wrap value of type %s"
                (Gil_syntax.Type.str typ)
        in
        { enc with expr = construct expr; kind = Simple_wrapped }
    | Extended_wrapped ->
        let guard = Ext_lit_operations.Gil_sing_elem.recognize expr in
        let extra_asrts = guard :: extra_asrts in
        let expr = Ext_lit_operations.Gil_sing_elem.access expr in
        { enc with extra_asrts; expr; kind = Simple_wrapped }

  let extend_wrap ({ expr; kind; _ } as enc) =
    require_definition def_gil_ext_literal;
    match kind with
    | Extended_wrapped -> enc
    | Native SetType ->
        let expr = Ext_lit_operations.Gil_set.construct expr in
        { enc with expr; kind = Extended_wrapped }
    | _ ->
        let enc = simple_wrap enc in
        let expr = Ext_lit_operations.Gil_sing_elem.construct enc.expr in
        { enc with expr; kind = Extended_wrapped }

  include struct
    open Lit_operations

    let get_bool =
      get_native ~accessor:Bool.access ~recognizer:Bool.recognize
        ~typ:BooleanType

    let get_int =
      get_native ~accessor:Int.access ~recognizer:Int.recognize ~typ:IntType

    let get_num =
      get_native ~accessor:Num.access ~recognizer:Num.recognize ~typ:NumberType

    let get_string =
      get_native ~accessor:String.access ~recognizer:String.recognize
        ~typ:StringType

    let get_utf16 =
      get_native ~accessor:Utf16String.access ~recognizer:Utf16String.recognize
        ~typ:Utf16Type

    let get_loc =
      get_native ~accessor:Loc.access ~recognizer:Loc.recognize ~typ:ObjectType

    let get_list =
      get_native ~accessor:List.access ~recognizer:List.recognize ~typ:ListType

    let get_type =
      get_native ~accessor:Type.access ~recognizer:Type.recognize ~typ:TypeType
  end

  let get_set ({ kind; expr; extra_asrts; _ } as enc) : t =
    match kind with
    | Native SetType ->
        require_definition def_gil_literal;
        enc
    | Extended_wrapped ->
        require_definition def_gil_ext_literal;
        let guard = Ext_lit_operations.Gil_set.recognize expr in
        let extra_asrts = guard :: extra_asrts in
        let expr = Ext_lit_operations.Gil_set.access expr in
        let kind = Native SetType in
        { enc with kind; extra_asrts; expr }
    | _ -> exceptf "wrong encoding of set"

  let get_datatype name =
    let (module V : Variant.Unary) = Datatype_operations.encode_datatype name in
    get_native ~accessor:V.access ~recognizer:V.recognize
      ~typ:(DatatypeType name)

  let get_native_of_type = function
    | Type.BooleanType -> get_bool
    | IntType -> get_int
    | NumberType -> get_num
    | StringType -> get_string
    | Utf16Type -> get_utf16
    | ObjectType -> get_loc
    | ListType -> get_list
    | TypeType -> get_type
    | DatatypeType name -> get_datatype name
    | (UndefinedType | NullType | EmptyType | NoneType | SetType) as typ ->
        Fmt.failwith "Cannot get native value of type %s"
          (Gil_syntax.Type.str typ)
end

let typeof_simple e =
  require_definition def_gil_literal;
  let open Type in
  let guards =
    Lit_operations.
      [
        (Null.recognize, NullType);
        (Empty.recognize, EmptyType);
        (Undefined.recognize, UndefinedType);
        (None.recognize, NoneType);
        (Bool.recognize, BooleanType);
        (Int.recognize, IntType);
        (Num.recognize, NumberType);
        (String.recognize, StringType);
        (Utf16String.recognize, Utf16Type);
        (Loc.recognize, ObjectType);
        (Type.recognize, TypeType);
        (List.recognize, ListType);
      ]
  in
  List.fold_left
    (fun acc (guard, typ) -> ite (guard e) (encode_type typ) acc)
    (encode_type UndefinedType)
    guards

let typeof_extended e =
  require_definition def_gil_ext_literal;
  let open Ext_lit_operations in
  let guard = Gil_set.recognize e in
  let typeof_simple = e |> Gil_sing_elem.access |> typeof_simple in
  ite guard (encode_type SetType) typeof_simple

let typeof_expression ({ kind; expr; _ } : Encoding.t) =
  match kind with
  | Native typ -> encode_type typ
  | Simple_wrapped -> typeof_simple expr
  | Extended_wrapped -> typeof_extended expr

module RepeatCache = struct
  let cache : (sexp * sexp, Encoding.t) Hashtbl.t = Hashtbl.create 0
  let var_counter = ref 0
  let make_var counter = "__repeat_var_" ^ string_of_int counter

  let next_var () =
    let ret = !var_counter in
    let () = incr var_counter in
    make_var ret

  let clear_var_counter () = var_counter := 0
  let index = atom "__index__"

  let clear () =
    let () = Hashtbl.clear cache in
    clear_var_counter ()

  let get_constraints var x n =
    let at_index_is_x = eq (seq_nth var index) x in
    let length = seq_len var in
    let all_eq_x = forall' [ (index, t_int) ] at_index_is_x in
    let length_is_n = eq length n in
    [ all_eq_x; length_is_n ]

  let get x n : Encoding.t =
    let- () = Hashtbl.find_opt cache (x, n) in
    let var = next_var () in
    let e = atom var in
    let extra_asrts = get_constraints e x n in
    let () = Hashtbl.add cache (x, n) (Encoding.native ListType e) in
    Encoding.native_const ~extra_asrts ListType var
end

let rec encode_lit (lit : Literal.t) : Encoding.t =
  let open Encoding in
  try
    match lit with
    | Undefined | Null | Empty | Nono -> (
        (* These encode directly to GIL_Literal constructors. *)
        require_definition def_gil_literal;
        match lit with
        | Undefined -> undefined_encoding
        | Null -> null_encoding
        | Empty -> empty_encoding
        | _ -> none_encoding)
    | Bool b -> bool_k b >- BooleanType
    | Int i -> int_zk i >- IntType
    | Num n -> number_literal n >- NumberType
    | Utf16String s ->
        require_definition Axiomatised_operations.def_utf162num;
        let bytes = Utils.Utf16.to_canonical s in
        let encoded = Utf16.encode bytes in
        let parsed = Axiomatised_operations.utf162num <| encoded in
        let value = number_literal (Arith_utils.string_to_number bytes) in
        native ~facts:[ eq parsed value ] Utf16Type encoded
    | String s ->
        require_definition Axiomatised_operations.def_str2num;
        let encoded = encode_string s in
        (* Ground parser facts must travel with literals even when they occur
           inside native sets/sequences. Otherwise formatter roundtrip facts
           still permit, for example, an integer key to equal "push". *)
        let parsed = Axiomatised_operations.str2num <| encoded in
        let value = number_literal (Arith_utils.string_to_number s) in
        native ~facts:[ eq parsed value ] StringType encoded
    | Loc l -> encode_symbol l >- ObjectType
    | Type t -> encode_type t >- TypeType
    | LList lits ->
        require_definition def_gil_literal;
        let>-- args = List.map (fun lit -> simple_wrap (encode_lit lit)) lits in
        let args = List.map (fun arg -> arg.expr) args in
        seq_of ~typ:t_gil_literal_list args >- ListType
    | Constant c -> (
        match Literal.static_constant c with
        | Some value -> encode_lit value
        | None ->
            raise (Exceptions.Unsupported "Z3 encoding: dynamic constants"))
  with Failure msg -> exceptf "DEATH: encode_lit %a. %s" Literal.pp lit msg

let wrapped_equality a b =
  let open Lit_operations in
  ite
    (bool_and (Num.recognize a) (Num.recognize b))
    (fp_bin "fp.eq" (Num.access a) (Num.access b))
    (eq a b)

let extended_equality a b =
  let open Ext_lit_operations in
  ite
    (bool_and (Gil_sing_elem.recognize a) (Gil_sing_elem.recognize b))
    (wrapped_equality (Gil_sing_elem.access a) (Gil_sing_elem.access b))
    (eq a b)

let encode_equality (p1 : Encoding.t) (p2 : Encoding.t) : Encoding.t =
  let open Encoding in
  let>- _ = p1 in
  let>- _ = p2 in
  match (p1.kind, p2.kind) with
  | Native t1, Native t2 when Type.equal t1 t2 ->
      let expr =
        match t1 with
        | NumberType -> fp_bin "fp.eq" p1.expr p2.expr
        | IntType | ListType ->
            let operand_key expression =
              let priority =
                match (t1, expression) with
                | IntType, Sexplib.Sexp.List (Sexplib.Sexp.Atom "ite" :: _) -> 0
                | _ -> 1
              in
              (priority, expression)
            in
            let left, right =
              if Stdlib.compare (operand_key p1.expr) (operand_key p2.expr) <= 0
              then (p1.expr, p2.expr)
              else (p2.expr, p1.expr)
            in
            eq left right
        | BooleanType when is_true p1.expr -> p2.expr
        | BooleanType when is_true p2.expr -> p1.expr
        | _ -> eq p1.expr p2.expr
      in
      expr >- BooleanType
  | Simple_wrapped, Simple_wrapped ->
      wrapped_equality p1.expr p2.expr >- BooleanType
  | Extended_wrapped, Extended_wrapped ->
      extended_equality p1.expr p2.expr >- BooleanType
  | Native Utf16Type, Native _ | Native _, Native Utf16Type ->
      bool_k false >- BooleanType
  | Native _, Native _ -> exceptf "incompatible equality, type error!"
  | Simple_wrapped, Native _ | Native _, Simple_wrapped ->
      let>- p1 = simple_wrap p1 in
      let>- p2 = simple_wrap p2 in
      wrapped_equality p1.expr p2.expr >- BooleanType
  | Extended_wrapped, _ | _, Extended_wrapped ->
      let>- p1 = extend_wrap p1 in
      let>- p2 = extend_wrap p2 in
      extended_equality p1.expr p2.expr >- BooleanType

(* Exact canonical Uint32 decimal parsing, array-index classification and
   structural insertion position. The
   recursive SMT function strips one key per call. No object-size bound, FP
   conversion, user axiom or inferred creation-order history is used. *)
(* Keep the quantified index local to a function definition. Inlining a
   fixed binder around the caller's encoded list could capture a free name. *)
let def_list_all_utf16 =
  let xs = atom "keys" and i = atom "index" in
  let condition = bool_implies
    (bool_and (num_leq (int_k 0) i) (num_lt i (seq_len xs)))
    (Lit_operations.Utf16String.recognize (seq_nth xs i)) in
  make_definition ~depends_on:[ def_gil_literal ]
    [ define_fun "gil_list_all_utf16" [ ("keys", t_gil_literal_list) ] t_bool
        (forall [ ("index", t_int) ] condition) ]

let def_key_insert_index =
  let name = atom "name" in
  let decimal_case length =
    let units = List.init length (fun i -> app_ "bv2int" [ seq_nth name (int_k i) ]) in
    let number = List.fold_left
      (fun prefix unit -> num_add (num_mul prefix (int_k 10)) (num_sub unit (int_k 48)))
      (int_k 0) units in
    let digits = List.map (fun unit -> bool_and (num_leq (int_k 48) unit) (num_leq unit (int_k 57))) units in
    let canonical = if length = 1 then atom "true" else bool_not (eq (List.hd units) (int_k 48)) in
    let valid = List.fold_left bool_and (eq (seq_len name) (int_k length))
      (canonical :: num_leq number (int_zk (Z.of_string "4294967295")) :: digits) in
    valid, number
  in
  let cases = List.init 10 (fun i -> decimal_case (i + 1)) in
  let decimal = List.fold_right (fun (valid, number) other -> ite valid number other) cases (int_k (-1)) in
  let parsed = app_ "gil_uint32_decimal_value" [ name ] in
  let index = ite (num_lt parsed (int_zk (Z.of_string "4294967295"))) parsed (int_k (-1)) in
  make_definition ~depends_on:[ def_gil_literal ]
    [ define_fun "gil_uint32_decimal_value" [ ("name", Utf16.sort) ] t_int decimal;
      define_fun "gil_key_index" [ ("name", Utf16.sort) ] t_int index;
      Sexplib.Sexp.of_string
        {smt|(define-fun-rec gil_index_position ((keys (Seq GIL_Literal)) (index Int)) Int
          (ite (= (seq.len keys) 0) 0
            (let ((head (seq.nth keys 0)))
              (let ((other (ite (isUtf16String head) (gil_key_index (u16Value head)) (- 1))))
                (ite (or (< other 0) (> other index)) 0
                  (+ 1 (gil_index_position (seq.extract keys 1 (- (seq.len keys) 1)) index)))))))|smt} ]

(* Exact UTF-16 trim, defined rather than axiomatized. A nonempty whitespace
   edge is removed before each recursive call, so seq.len decreases by one.
   Indices and lengths are mathematical Ints; no FP rounding or size bound is
   introduced. The guarded empty case never observes an out-of-range unit.
   The 25 units are exactly Utils.Utf16.is_space's current concrete table. *)
let def_utf16_trim =
  let unit = atom "unit" in
  let whitespace = Utils.Utf16.whitespace_code_units in
  let is_space =
    List.fold_left
      (fun result code -> bool_or result (eq unit (bv_k 16 (Z.of_int code))))
      (bool_k false) whitespace
  in
  make_definition
    [ define_fun "gil_utf16_whitespace" [ ("unit", t_bits 16) ] t_bool is_space;
      Sexplib.Sexp.of_string
        {smt|(define-fun-rec gil_utf16_trim_left ((input (Seq (_ BitVec 16)))) (Seq (_ BitVec 16))
          (ite (= (seq.len input) 0) input
            (ite (gil_utf16_whitespace (seq.nth input 0))
              (gil_utf16_trim_left (seq.extract input 1 (- (seq.len input) 1)))
              input)))|smt};
      Sexplib.Sexp.of_string
        {smt|(define-fun-rec gil_utf16_trim_right ((input (Seq (_ BitVec 16)))) (Seq (_ BitVec 16))
          (ite (= (seq.len input) 0) input
            (ite (gil_utf16_whitespace (seq.nth input (- (seq.len input) 1)))
              (gil_utf16_trim_right (seq.extract input 0 (- (seq.len input) 1)))
              input)))|smt};
      define_fun "gil_utf16_trim" [ ("input", Utf16.sort) ] Utf16.sort
        (app_ "gil_utf16_trim_right"
           [ app_ "gil_utf16_trim_left" [ atom "input" ] ]) ]

let encode_binop (op : BinOp.t) (p1 : Encoding.t) (p2 : Encoding.t) : Encoding.t
    =
  let open Encoding in
  let>- _ = p1 in
  let>- _ = p2 in
  (* In the case of strongly typed operations, we do not perform any check.
     Type checking has happened before reaching z3, and therefore, isn't required here again.
     An unknown type is represented by the [None] variant of the option type.
     It is expected that values of unknown type are already wrapped into their constructors.
  *)
  match op with
  | IPlus ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_add p1.expr p2.expr >- IntType
  | IMinus ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_sub p1.expr p2.expr >- IntType
  | ITimes ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_mul p1.expr p2.expr >- IntType
  | IDiv ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      integer_quotient p1.expr p2.expr >- IntType
  | IMod ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_sub p1.expr (num_mul p2.expr (integer_quotient p1.expr p2.expr))
      >- IntType
  | ILessThan ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_lt p1.expr p2.expr >- BooleanType
  | ILessThanEqual ->
      let>- p1 = get_int p1 in
      let>- p2 = get_int p2 in
      num_leq p1.expr p2.expr >- BooleanType
  | FPlus ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_arith "fp.add" p1.expr p2.expr >- NumberType
  | FMinus ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_arith "fp.sub" p1.expr p2.expr >- NumberType
  | FTimes ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_arith "fp.mul" p1.expr p2.expr >- NumberType
  | FDiv ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_arith "fp.div" p1.expr p2.expr >- NumberType
  | FLessThan ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_bin "fp.lt" p1.expr p2.expr >- BooleanType
  | FLessThanEqual ->
      let>- p1 = get_num p1 in
      let>- p2 = get_num p2 in
      fp_bin "fp.leq" p1.expr p2.expr >- BooleanType
  | ValueEqual ->
      (* Native datatype equality is reflexive at NaN and distinguishes zeros,
         including numbers nested inside sequences or constructors. *)
      let>- p1 = extend_wrap p1 in
      let>- p2 = extend_wrap p2 in
      eq p1.expr p2.expr >- BooleanType
  | Equal -> encode_equality p1 p2
  | Or ->
      let>- p1 = get_bool p1 in
      let>- p2 = get_bool p2 in
      bool_or p1.expr p2.expr >- BooleanType
  | Impl ->
      let>- p1 = get_bool p1 in
      let>- p2 = get_bool p2 in
      bool_implies p1.expr p2.expr >- BooleanType
  | And ->
      let>- p1 = get_bool p1 in
      let>- p2 = get_bool p2 in
      bool_and p1.expr p2.expr >- BooleanType
  | SetMem ->
      (* p2 has to be already wrapped *)
      let>- p1 = simple_wrap p1 in
      let>- p2 = get_set p2 in
      set_member Z3 p1.expr p2.expr >- BooleanType
  | SetDiff ->
      let>- p1 = get_set p1 in
      let>- p2 = get_set p2 in
      set_difference Z3 p1.expr p2.expr >- SetType
  | SetSub ->
      let>- p1 = get_set p1 in
      let>- p2 = get_set p2 in
      set_subset Z3 p1.expr p2.expr >- BooleanType
  | LstNth ->
      let>- p1 = get_list p1 in
      let>- p2 = get_int p2 in
      seq_nth p1.expr p2.expr |> simply_wrapped
  | KeyInsertIndex ->
      require_definition def_key_insert_index;
      let>- keys = get_list p1 in
      let>- name = get_utf16 p2 in
      let index = app_ "gil_key_index" [ name.expr ] in
      let length = seq_len keys.expr in
      let position = ite (num_lt index (int_k 0)) length
          (app_ "gil_index_position" [ keys.expr; index ]) in
      let last = seq_nth keys.expr (num_sub length (int_k 1)) in
      let last_index = ite (Lit_operations.Utf16String.recognize last)
          (app_ "gil_key_index" [ Lit_operations.Utf16String.access last ])
          (int_k (-1)) in
      (* Induction on the finite key suffix: if its final element stops the
         scan, the first stop is at most length-1. This is a consequence of
         gil_index_position, not an order/ownership assumption about the list.
         Empty lists, ordinary inserted names, and a smaller terminal index
         must retain their possible position == length. *)
      let stops_at_last = bool_and (num_lt (int_k 0) length)
          (bool_and (num_leq (int_k 0) index)
             (bool_or (num_lt last_index (int_k 0)) (num_lt index last_index))) in
      native ~facts:[ num_leq (int_k 0) position; num_leq position length;
          bool_implies stops_at_last (num_lt position length) ]
        IntType position
  | LstContains ->
      let>- list = get_list p1 in
      let>- value = simple_wrap p2 in
      (* Sequence membership is native datatype equality, exactly as v==. *)
      app (atom "seq.contains") [ list.expr; seq_unit value.expr ] >- BooleanType
  | LstRepeat ->
      let>- x = simple_wrap p1 in
      let>- n = get_int p2 in
      RepeatCache.get x.expr n.expr
  | StrCat ->
      let>- left = get_string p1 in
      let>- right = get_string p2 in
      seq_concat [ left.expr; right.expr ] >- StringType
  | Utf16Cat ->
      let>- left = get_utf16 p1 in
      let>- right = get_utf16 p2 in
      seq_concat [ left.expr; right.expr ] >- Utf16Type
  | (Utf16Nth | Utf16CodeUnit) as op ->
      if not !Config.Verification.total then
        exceptf
          "SMT encoding: symbolic UTF-16 indexing requires total-mode domain \
           checks";
      let>- str = get_utf16 p1 in
      let>- index = get_num p2 in
      let unit = seq_nth str.expr (number_to_integer index.expr) in
      if op = Utf16Nth then seq_unit unit >- Utf16Type
      else
        (* Every unsigned 16-bit unit is exactly representable as binary64.
           The same checked index domain guards both observations. *)
        app
          (List [ atom "_"; atom "to_fp_unsigned"; atom "11"; atom "53" ])
          [ rne; unit ]
        >- NumberType
  | StrNth ->
      require_definition Axiomatised_operations.def_snth;
      let>- str' = get_string p1 in
      let>- index' = get_num p2 in
      let res = Axiomatised_operations.snth $$ [ str'.expr; index'.expr ] in
      res >- StringType
  | BitwiseAndF ->
      let>- left = get_num p1 in
      let>- right = get_num p2 in
      (* Number AND applies ToInt32 to both operands. Modular conversion is
         total even for NaN/infinities, and every signed 32-bit result is
         exactly representable as binary64. CExprEval uses the same domain. *)
      let bits =
        app_ "bvand"
          [
            integer_wrap_bits ~width:32 left.expr;
            integer_wrap_bits ~width:32 right.expr;
          ]
      in
      app (List [ atom "_"; atom "to_fp"; atom "11"; atom "53" ]) [ rne; bits ]
      >- NumberType
  | FMod
  | Utf16Less
  | StrLess
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | LeftShift
  | SignedRightShift
  | UnsignedRightShift
  | BitwiseAndL
  | BitwiseOrL
  | BitwiseXorL
  | LeftShiftL
  | SignedRightShiftL
  | UnsignedRightShiftL
  | BitwiseOrF
  | BitwiseXorF
  | LeftShiftF
  | SignedRightShiftF
  | UnsignedRightShiftF
  | M_atan2
  | M_pow ->
      exceptf "SMT encoding: Costruct not supported yet - binop: %s"
        (BinOp.str op)

let encode_unop ~llen_lvars ~e (op : UnOp.t) le =
  let open Encoding in
  let open Axiomatised_operations in
  let>- _ = le in
  match op with
  | IUnaryMinus ->
      let>- le = get_int le in
      num_neg le.expr >- IntType
  | FUnaryMinus ->
      let>- le = get_num le in
      fp_un "fp.neg" le.expr >- NumberType
  | LstLen ->
      (* If we only use an LVar as an argument to llen, then encode it as an uninterpreted function. *)
      let>- le = get_list le in
      let enc =
        match e with
        | Expr.LVar l when SS.mem l llen_lvars ->
            require_definition def_llen;
            llen <| le.expr
        | _ -> seq_len le.expr
      in
      enc >- IntType
  | LstAllUtf16 ->
      require_definition def_list_all_utf16;
      let>- xs = get_list le in
      app_ "gil_list_all_utf16" [ xs.expr ] >- BooleanType
  | StrToBytes ->
      require_definition def_gil_literal;
      let>- bytes = get_string le in
      let byte = atom "byte_value" in
      let value =
        Lit_operations.Num.construct
          (app
             (List [ atom "_"; atom "to_fp_unsigned"; atom "11"; atom "53" ])
             [ rne; byte ])
      in
      let mapping =
        list [ atom "lambda"; list [ list [ byte; t_byte ] ]; value ]
      in
      app_ "seq.map" [ mapping; bytes.expr ] >- ListType
  | StrLen ->
      require_definition def_slen;
      let>- le = get_string le in
      slen <| le.expr >- NumberType
  | Utf16Len ->
      let>- le = get_utf16 le in
      seq_len le.expr >- IntType
  | Utf16Trim ->
      require_definition def_utf16_trim;
      let>- le = get_utf16 le in
      app_ "gil_utf16_trim" [ le.expr ] >- Utf16Type
  | ToStringOp | NumberToUtf16 ->
      let num2str, str2num, encode_string, typ =
        if op = NumberToUtf16 then (
          require_definition def_num2utf16;
          require_definition def_utf162num;
          (num2utf16, utf162num, Utf16.encode, Type.Utf16Type))
        else (
          require_definition def_num2str;
          require_definition def_str2num;
          (num2str, str2num, encode_string, Type.StringType))
      in
      let>- le = get_num le in
      (* JavaScript formatting identifies signed zeros. Outside integral
         Uint32 Numbers the finite symbolic formatter remains opaque. *)
      let formatted =
        ite
          (fp_un "fp.isZero" le.expr)
          (encode_string "0")
          (ite (fp_un "fp.isNaN" le.expr) (encode_string "NaN")
             (ite
                (fp_un "fp.isInfinite" le.expr)
                (ite
                   (fp_un "fp.isNegative" le.expr)
                   (encode_string "-Infinity")
                   (encode_string "Infinity"))
                (num2str <| le.expr)))
      in
      (* Every formatter-produced spelling parses back to the same number;
         numeric equality identifies signed zeros, and NaN needs its own test.
         Keep this fact with the encoded term so native set/sequence reasoning
         can distinguish numeric keys without reconstructing the formatter. *)
      let parsed = str2num <| formatted in
      let roundtrip =
        bool_or
          (fp_bin "fp.eq" parsed le.expr)
          (bool_and (fp_un "fp.isNaN" parsed) (fp_un "fp.isNaN" le.expr))
      in
      let facts =
        if op = NumberToUtf16 then (
          require_definition def_key_insert_index;
          let in_range = bool_and
              (fp_bin "fp.leq" (number_literal 0.) le.expr)
              (fp_bin "fp.leq" le.expr (number_literal 4294967295.)) in
          let integral = fp_bin "fp.eq" le.expr
              (app_ "fp.roundToIntegral" [ atom "RTZ"; le.expr ]) in
          let exact = bool_and in_range integral in
          let bits = app (list [ atom "_"; atom "fp.to_ubv"; atom "32" ])
              [ atom "RTZ"; ite exact le.expr (number_literal 0.) ] in
          (* The decimal recognizer has exactly one spelling for each Uint32:
             1..10 decimal digits, no leading zeros, with value <= 2^32-1.
             Constraining that defined relation precisely models the formatter
             on this interval without expanding the construction of its digits.
             It does not give opaque names an assumed array-index class. *)
          bool_implies exact
            (eq (app_ "gil_uint32_decimal_value" [ formatted ])
               (app_ "bv2int" [ bits ])) :: [ roundtrip ])
        else [ roundtrip ]
      in
      native ~facts typ formatted
  | Utf16ToNumber ->
      require_definition def_utf162num;
      let>- le = get_utf16 le in
      utf162num <| le.expr >- NumberType
  | ToNumberOp ->
      require_definition def_str2num;
      let>- le = get_string le in
      Axiomatised_operations.str2num <| le.expr >- NumberType
  | ToIntOp ->
      let>- le = get_num le in
      (* The runtime's ToInteger preserves infinities and signed zero, maps
         NaN to +0, and otherwise truncates toward zero. *)
      ite (fp_un "fp.isNaN" le.expr) (number_literal 0.)
        (app_ "fp.roundToIntegral" [ atom "RTZ"; le.expr ])
      >- NumberType
  | ToUint32Op | ToUint16Op | ToInt32Op ->
      let>- le = get_num le in
      integer_wrap
        ~width:(if op = ToUint16Op then 16 else 32)
        ~signed:(op = ToInt32Op) le.expr
      >- NumberType
  | Not ->
      let>- le = get_bool le in
      bool_not le.expr >- BooleanType
  | Cdr ->
      let>- list = get_list le in
      seq_extract list.expr (int_k 1) (seq_len list.expr) >- ListType
  | Car ->
      let>- list = get_list le in
      seq_nth list.expr (int_k 0) |> simply_wrapped
  | TypeOf -> typeof_expression le >- TypeType
  | LstRev ->
      require_definition def_lrev;
      let>- le = get_list le in
      Axiomatised_operations.lrev <| le.expr >- ListType
  | BoolToInt ->
      let>- le = get_bool le in
      ite le.expr (int_k 1) (int_k 0) >- IntType
  | NumToInt ->
      (* Total-mode execution checks finiteness before evaluating this partial
         conversion. The guarded native conversion and its exact fp.to_real
         fallback produce the required integer on finite values. Logical
         nonfinite terms have an unspecified integer extension; they cannot bypass that execution
         check. Keep the previous restriction in ordinary mode, whose domain
         checks have not been audited. Nonfinite literals remain rejected. *)
      (match e with
      | Expr.Lit (Num n) when Float.is_finite n -> ()
      | Expr.Lit _ ->
          exceptf "SMT encoding: NumToInt requires a finite concrete operand"
      | _ when !Config.Verification.total -> ()
      | _ -> exceptf "SMT encoding: NumToInt requires a finite concrete operand");
      let>- le = get_num le in
      let ordinary = number_to_integer_count le.expr in
      let integer = match e, le.expr with
        | Expr.BinOp (_, FPlus, Lit (Num 1.)),
          List [ Atom "fp.add"; Atom "RNE"; counter; _ ] ->
            (* Every integral counter in [0, 2^32-1) and its successor are
               exactly representable binary64 integers. RTZ(counter + 1)
               therefore equals RTZ(counter) + 1. Keep an actual SMT guard:
               fractions, negative counters, nonfinite values and larger
               integers retain the original FP addition/conversion. Operand
               typing and encoding facts have already been retained above. *)
            let integral = fp_bin "fp.eq" counter
              (app_ "fp.roundToIntegral" [ atom "RTZ"; counter ]) in
            let range = bool_and
              (fp_bin "fp.leq" (number_literal 0.) counter)
              (fp_bin "fp.lt" counter (number_literal 4294967295.)) in
            ite (bool_and integral range)
              (num_add (number_to_integer_count counter) (int_k 1)) ordinary
        | Expr.BinOp (_, FMinus, Expr.BinOp (_, FPlus, Lit (Num 1.))),
          List [ Atom "fp.sub"; Atom "RNE"; left;
            List [ Atom "fp.add"; Atom "RNE"; counter; _ ] ] ->
            (* Integral uint32 left and counter < 2^32-1 have an exact
               binary64 successor and signed difference. Reuse its integer
               successor directly instead of recasting raw FP addition.
               Signed zeros count as zero; every guard failure keeps the
               original FP subtraction/conversion without extra facts. *)
            let integral value = fp_bin "fp.eq" value
              (app_ "fp.roundToIntegral" [ atom "RTZ"; value ]) in
            let left_range = bool_and
              (fp_bin "fp.leq" (number_literal 0.) left)
              (fp_bin "fp.leq" left (number_literal 4294967295.)) in
            let counter_range = bool_and
              (fp_bin "fp.leq" (number_literal 0.) counter)
              (fp_bin "fp.lt" counter (number_literal 4294967295.)) in
            let guard = bool_and (bool_and (integral left) left_range)
              (bool_and (integral counter) counter_range) in
            ite guard
              (num_sub (number_to_integer_count left)
                 (num_add (number_to_integer_count counter) (int_k 1))) ordinary
        | Expr.BinOp (_, FMinus, _),
          List [ Atom "fp.sub"; Atom "RNE"; left; right ] ->
            (* Both integral operands in [0, 2^32-1] and their signed
               difference are exactly representable in binary64. RNE
               subtraction is therefore exact, so RTZ distributes here.
               The actual SMT guard keeps every other operand on the
               original FP subtraction/conversion path. *)
            let uint32_integer value =
              let integral = fp_bin "fp.eq" value
                (app_ "fp.roundToIntegral" [ atom "RTZ"; value ]) in
              let range = bool_and
                (fp_bin "fp.leq" (number_literal 0.) value)
                (fp_bin "fp.leq" value (number_literal 4294967295.)) in
              bool_and integral range in
            ite (bool_and (uint32_integer left) (uint32_integer right))
              (num_sub (number_to_integer_count left)
                 (number_to_integer_count right)) ordinary
        | _ -> ordinary in
      integer >- IntType
  | IntToNum ->
      let>- le = get_int le in
      let general = to_number [ rne; int_to_real le.expr ] in
      (match e with
      | Expr.UnOp (Utf16Len, _) ->
          (* Sequence length is nonnegative. Below 2^16, int2bv preserves it
             exactly and unsigned BV-to-FP is exact. Keep the general RNE
             conversion for every larger length, including overflow; this
             guard is an encoding choice, not a bound on the string domain. *)
          let small =
            app (List [ atom "_"; atom "int2bv"; atom "16" ]) [ le.expr ]
          in
          ite
            (num_lt le.expr (int_k 65536))
            (app
               (List [ atom "_"; atom "to_fp_unsigned"; atom "11"; atom "53" ])
               [ rne; small ])
            general
      | _ -> general)
      >- NumberType
  | IsInt ->
      let>- le = get_num le in
      bool_and (fp_finite le.expr)
        (fp_bin "fp.eq" le.expr
           (app_ "fp.roundToIntegral" [ atom "RTZ"; le.expr ]))
      >- BooleanType
  | M_isNaN ->
      let>- le = get_num le in
      fp_un "fp.isNaN" le.expr >- BooleanType
  | M_abs ->
      let>- le = get_num le in
      fp_un "fp.abs" le.expr >- NumberType
  | BitwiseNot
  | M_acos
  | M_asin
  | M_atan
  | M_ceil
  | M_cos
  | M_exp
  | M_floor
  | M_log
  | M_round
  | M_sgn
  | M_sin
  | M_sqrt
  | M_tan
  | SetToList ->
      let msg =
        Fmt.str "SMT encoding: Construct not supported yet - unop - %s!"
          (UnOp.str op)
      in
      let () = L.print_to_all msg in
      raise (Failure msg)

let copy_extend_gamma gamma vars =
  (* Start by updating gamma with the information provided by bound / quantifier types.
     There's very few foralls, so it's ok to copy the gamma entirely *)
  let gamma = Hashtbl.copy gamma in
  let () =
    vars
    |> List.iter (fun (x, typ) ->
           match typ with
           | None -> Hashtbl.remove gamma x
           | Some typ -> Hashtbl.replace gamma x typ)
  in
  (* Not the same gamma now!*)
  gamma

let encode_bound_expr
    ~(encode_expr :
       gamma:typenv ->
       llen_lvars:SS.t ->
       list_elem_vars:SS.t ->
       'a ->
       Encoding.t)
    ~gamma
    ~llen_lvars
    ~list_elem_vars
    bound_vars
    (expr : 'a) =
  let open Encoding in
  let gamma = copy_extend_gamma gamma bound_vars in
  let encoded = encode_expr ~gamma ~llen_lvars ~list_elem_vars expr in

  (* Extra asrts could contain these bound variables - separate these *)
  let rec atoms (sexp : sexp) =
    match sexp with
    | Atom s -> SS.singleton s
    | List lst -> List.fold_left SS.union SS.empty (List.map atoms lst)
  in
  let bs = SS.of_list (List.map fst bound_vars) in
  let contains_bound_vars asrt = not (SS.disjoint bs (atoms asrt)) in
  let bound_asrts, extra_asrts =
    List.partition contains_bound_vars encoded.extra_asrts
  in
  (* Case-bound primitive facts may safely be omitted (losing precision), but
     must not escape their binder as assertions about unrelated free names. *)
  let facts =
    List.filter (fun fact -> not (contains_bound_vars fact)) encoded.facts
  in
  let encoded = { encoded with extra_asrts; facts } in

  (* Don't declare consts for quantified vars *)
  let bound_vars =
    bound_vars
    |> List.map (fun (x, t) ->
           let sort =
             match t with
             | None -> t_gil_ext_literal
             | Some typ -> native_sort_of_type typ
           in
           (x, sort))
  in
  let () =
    encoded.consts
    |> Hashtbl.filter_map_inplace (fun c () ->
           if List.mem c bound_vars then None else Some ())
  in
  (bound_vars, bound_asrts, encoded)

let encode_quantified_expr
    ~(encode_expr :
       gamma:typenv ->
       llen_lvars:SS.t ->
       list_elem_vars:SS.t ->
       'a ->
       Encoding.t)
    ~mk_quant
    ~universal
    ~gamma
    ~llen_lvars
    ~list_elem_vars
    quantified_vars
    (assertion : 'a) : Encoding.t =
  let open Encoding in
  let- () =
    match quantified_vars with
    | [] ->
        (* A quantified assertion with no quantified variables is just the assertion *)
        Some (encode_expr ~gamma ~llen_lvars ~list_elem_vars assertion)
    | _ -> None
  in
  let gamma = copy_extend_gamma gamma quantified_vars in
  let encoded_assertion, consts, extra_asrts, facts =
    match encode_expr ~gamma ~llen_lvars ~list_elem_vars assertion with
    | { kind = Native BooleanType; expr; consts; extra_asrts; facts } ->
        (expr, consts, extra_asrts, facts)
    | _ -> exceptf "the thing inside forall is not boolean!"
  in
  let quantified_vars =
    quantified_vars
    |> List.map (fun (x, t) ->
           let sort =
             match t with
             | None -> t_gil_ext_literal
             | Some typ -> native_sort_of_type typ
           in
           (x, sort))
  in
  (* Don't declare consts for quantified vars *)
  let () =
    consts
    |> Hashtbl.filter_map_inplace (fun c () ->
           if List.mem c quantified_vars then None else Some ())
  in
  (* Primitive facts hold for every interpretation of the actual operation.
     Scope them under the binder without treating expression domain guards as
     intrinsic facts: those guards must not weaken universal assertions. *)
  let body =
    match facts with
    | [] -> encoded_assertion
    | _ ->
        let conditions = app_ "and" facts in
        if universal then app_ "=>" [ conditions; encoded_assertion ]
        else bool_and conditions encoded_assertion
  in
  let expr = mk_quant quantified_vars body in
  native ~consts ~extra_asrts BooleanType expr

let rec encode_logical_expression
    ~(gamma : typenv)
    ~(llen_lvars : SS.t)
    ~(list_elem_vars : SS.t)
    (le : Expr.t) : Encoding.t =
  let open Encoding in
  let f = encode_logical_expression ~gamma ~llen_lvars ~list_elem_vars in

  match le with
  | Lit lit -> encode_lit lit
  | LVar var ->
      let kind, typ =
        match Hashtbl.find_opt gamma var with
        | Some typ -> (Native typ, native_sort_of_type typ)
        | None ->
            if SS.mem var list_elem_vars then (
              require_definition def_gil_literal;
              (Simple_wrapped, t_gil_literal))
            else (
              require_definition def_gil_ext_literal;
              (Extended_wrapped, t_gil_ext_literal))
      in
      make_const ~typ kind var
  | ALoc var -> native_const ObjectType var
  | PVar _ -> exceptf "HORROR: Program variable in pure formula"
  | UnOp (ToInt32Op, (BinOp (_, Utf16CodeUnit, _) as unit)) ->
      (* Every numeric code unit is in [0, 65535], so ToInt32 preserves it.
         Encode the observation normally: retain receiver/index requirements
         and the total-mode gate; no lookup or operand is discarded. *)
      f unit
  | UnOp (IsInt, UnOp (ToIntOp, value)) ->
      (* ToInteger maps NaN to zero and truncates every finite Number to an
         integer, preserving signed zero. Only infinities remain non-integral.
         Evaluate the operand and retain its typing/definedness requirements;
         neither ToInteger's Number result nor the input domain changes. *)
      let>- value = get_num (f value) in
      bool_not (fp_un "fp.isInfinite" value.expr) >- BooleanType
  | UnOp (IsInt, UnOp (IntToNum, (UnOp (Utf16Len, _) as size))) ->
      (* A nonnegative integer rounds either to an integral finite binary64
         value or to +infinity. The overflow midpoint is 2^1024 - 2^970:
         max-finite = 2^1024 - 2^971, and the midpoint tie rounds to infinity.
         Thus IsInt(RNE64(length)) is exactly length < midpoint. This changes
         only the composite predicate, never the Number conversion or domain.
         See ECMAScript 2022 6.1.6.1 (Number representation / ties-to-even). *)
      let>- size = get_int (f size) in
      num_lt size.expr
        (int_zk (Z.sub (Z.shift_left Z.one 1024) (Z.shift_left Z.one 970)))
      >- BooleanType
  | UnOp
      ( Not,
        BinOp
          ( (UnOp (NumToInt, _) as offset),
            ILessThan,
            (UnOp (Utf16Len, _) as size) ) ) ->
      f (BinOp (size, ILessThanEqual, offset))
  | UnOp (op, le) -> encode_unop ~llen_lvars ~e:le op (f le)
  | BinOp
      ( Lit (Num zero),
        FLessThanEqual,
        UnOp (IntToNum, (UnOp (Utf16Len, _) as size)) )
    when zero = 0. ->
      (* RNE conversion of a nonnegative integer cannot be negative or NaN.
         Overflow produces +infinity, so this also holds for unbounded generic
         UTF-16 sequences. Both signs of zero compare equally. Evaluate the
         operand normally to retain its typing and definedness obligations. *)
      let>- size = get_int (f size) in
      num_leq (int_zk Z.zero) size.expr >- BooleanType
  | BinOp
      ( (UnOp (Utf16Len, _) as size),
        ILessThanEqual,
        (UnOp (NumToInt, pos) as offset) ) ->
      let>- offset = get_int (f offset) in
      let>- size_value = get_int (f size) in
      let>- pos_value = get_num (f pos) in
      let>- outside =
        get_bool (f (BinOp (UnOp (IntToNum, size), FLessThanEqual, pos)))
      in
      (* If finite nonnegative p < RNE(N), trunc(p) < N: otherwise
         N <= trunc(p) <= p and monotonic RNE gives RNE(N) <= p.
         The redundant conjunct exposes this contradiction in negated bound
         obligations. Positive bounds retain their direct integer encoding. *)
      bool_and
        (num_leq size_value.expr offset.expr)
        (bool_not
           (bool_and (fp_finite pos_value.expr)
              (bool_and
                 (fp_bin "fp.leq" (number_literal 0.) pos_value.expr)
                 (bool_not outside.expr))))
      >- BooleanType
  | BinOp
      ( UnOp (IntToNum, (UnOp (Utf16Len, _) as size)),
        FLessThanEqual,
        Lit (Num maximum) )
    when maximum = 9007199254740991. ->
      (* M = 2^53-1 is representable, as is every integer from 0 through M.
         For N >= M+1, monotonic RNE gives RNE(N) >= 2^53, also at overflow.
         Thus RNE64(N) <= M iff N <= M. This exact cutoff does not generalize
         to 2^53, since 2^53+1 rounds down. Keep conversion unchanged and
         encode the operand normally, retaining its typing/domain guards. *)
      let>- size = get_int (f size) in
      num_leq size.expr (int_zk (Z.pred (Z.shift_left Z.one 53))) >- BooleanType
  | BinOp ((UnOp (IntToNum, UnOp (Utf16Len, _)) as len), FLessThanEqual, pos) ->
      let>- len = get_num (f len) in
      let>- pos = get_num (f pos) in
      (* Rounded sequence lengths are nonnegative, including overflow. This
         redundant conjunct exposes the impossible negative-position case
         without restricting any input or adding facts to other expressions.
         NaN still makes the original comparison false; operand guards remain. *)
      bool_and
        (bool_not (fp_bin "fp.lt" pos.expr (number_literal 0.)))
        (fp_bin "fp.leq" len.expr pos.expr)
      >- BooleanType
  | BinOp
      ( (UnOp (NumToInt,
           BinOp ((LVar _ as n), FMinus, (LVar _ as i))) as difference),
        ILessThan, Lit (Int zero) )
    when Z.equal zero Z.zero && !Config.Verification.total ->
      (* Reuse the direct subtraction's actual integral uint32 guard. Both
         operands and their difference are exact binary64 integers there,
         so its converted count is negative iff n < i. Signed zeros count
         as zero. Every failed guard keeps the complete integer comparison;
         an FP sign test alone is unsound for fractional differences. *)
      let>- converted = get_int (f difference) in
      let ordinary = num_lt converted.expr (int_k 0) in
      (match converted.expr with
      | List [ Atom "ite"; guard; _; _ ] ->
          let>- n = get_num (f n) in
          let>- i = get_num (f i) in
          ite guard (fp_bin "fp.lt" n.expr i.expr) ordinary >- BooleanType
      | _ -> ordinary >- BooleanType)
  | BinOp
      ( (UnOp
           ( NumToInt,
             BinOp ((LVar _ as n), FMinus,
               BinOp ((LVar _ as i), FPlus, Lit (Num 1.))) ) as difference),
        ILessThan,
        Lit (Int zero) )
    when Z.equal zero Z.zero && !Config.Verification.total ->
      (* Reuse the conversion's actual guard and keep its facts/domain checks.
         Under that guard n and i are integral uint32 values, i+1 is exact,
         and the signed difference is exact. Its integer count is negative
         iff n < i+1. Fractions and every guard failure retain the complete
         original integer comparison; testing the FP sign there is unsound. *)
      let>- converted = get_int (f difference) in
      let ordinary = num_lt converted.expr (int_k 0) in
      (match converted.expr with
      | List [ Atom "ite"; guard; _; _ ] ->
          let>- n = get_num (f n) in
          let>- i = get_num (f i) in
          ite guard
            (fp_bin "fp.lt" n.expr
               (fp_arith "fp.add" i.expr (number_literal 1.)))
            ordinary
          >- BooleanType
      | _ -> ordinary >- BooleanType)
  | BinOp (le1, op, le2) -> encode_binop op (f le1) (f le2)
  | NOp (SetUnion, les) ->
      let>-- les = List.map f les in
      let>-- sets = List.map get_set les in
      let sets = List.map (fun set -> set.expr) sets in
      set_union' Z3 sets >- SetType
  | NOp (SetInter, les) ->
      let>-- les = List.map f les in
      let>-- sets = List.map get_set les in
      let sets = List.map (fun set -> set.expr) sets in
      set_intersection' Z3 sets >- SetType
  | NOp (Utf16Sub, [ text; start; count ]) ->
      let>- text = f text in
      let>- start = f start in
      let>- count = f count in
      let>- text = get_utf16 text in
      let>- start = get_int start in
      let>- count = get_int count in
      (* TOTAL proves the valid slice domain before matching/evaluating this
         proof expression. No clamping fact or nonexpansion axiom is added. *)
      seq_extract text.expr start.expr count.expr >- Utf16Type
  | NOp (Utf16Sub, _) -> exceptf "UTF-16 slice requires exactly three arguments"
  | NOp (LstInsert, [ xs; i; value ]) ->
      let>- xs = f xs in
      let>- i = f i in
      let>- value = f value in
      let>- xs = get_list xs in
      let>- i = get_int i in
      let>- value = simple_wrap value in
      let length = seq_len xs.expr in
      let inserted = seq_concat [ seq_extract xs.expr (int_k 0) i.expr;
        seq_unit value.expr;
        seq_extract xs.expr i.expr (num_sub length i.expr) ] in
      (* With 0 <= i < length, the nonempty suffix still ends in the old final
         element, now at index length. Keep this exact sequence consequence
         separate from heap ownership and from the append case i == length. *)
      let before_end = bool_and (num_leq (int_k 0) i.expr)
          (num_lt i.expr length) in
      let in_bounds = bool_and (num_leq (int_k 0) i.expr)
          (num_leq i.expr length) in
      (* The two in-range slices have lengths i and length-i. Their singleton
         insertion therefore adds exactly one, including at either endpoint. *)
      native ~facts:[ bool_implies in_bounds
          (eq (seq_len inserted) (num_add length (int_k 1)));
          bool_implies before_end
          (eq (seq_nth inserted length)
             (seq_nth xs.expr (num_sub length (int_k 1)))) ]
        ListType inserted
  | NOp (LstInsert, _) -> exceptf "List insertion requires exactly three arguments"
  | NOp (LstCat, les) ->
      let>-- les = List.map f les in
      let>-- lists = List.map get_list les in
      let lists = List.map (fun list -> list.expr) lists in
      seq_concat lists >- ListType
  | EList les ->
      let>-- args = List.map f les in
      let>-- args = List.map simple_wrap args in
      let args = List.map (fun arg -> arg.expr) args in
      seq_of ~typ:t_gil_literal_list args >- ListType
  | ESet les ->
      let>-- args = List.map f les in
      let>-- args = List.map simple_wrap args in
      let args = List.map (fun arg -> arg.expr) args in
      set_of args >- SetType
  | LstSub (lst, start, len) ->
      let>- lst = f lst in
      let>- start = f start in
      let>- len = f len in
      let>- lst = get_list lst in
      let>- start = get_int start in
      let>- len = get_int len in
      seq_extract lst.expr start.expr len.expr >- ListType
  | Exists (bt, e) ->
      encode_quantified_expr ~encode_expr:encode_logical_expression
        ~mk_quant:exists ~universal:false ~gamma ~llen_lvars ~list_elem_vars bt
        e
  | ForAll (bt, e) ->
      encode_quantified_expr ~encode_expr:encode_logical_expression
        ~mk_quant:forall ~universal:true ~gamma ~llen_lvars ~list_elem_vars bt e
  | FuncApp (name, les) ->
      let param_types =
        match Function_env.get_function_param_types name with
        | None -> exceptf "SMT - Undefined function %s" name
        | Some ps -> ps
      in
      let extend_wrap_or_native = function
        | Some typ -> get_native_of_type typ
        | None -> extend_wrap
      in
      let>-- args = List.map f les in
      let>-- args = List.map2 extend_wrap_or_native param_types args in
      let args = List.map (fun arg -> arg.expr) args in
      extended_wrapped (app_ name args)
  | Cases (le, cs) ->
      (* Type checking should ensure that all constructors belong to the same datatype *)
      let constructors_t =
        match cs with
        | (cname, _, _) :: _ ->
            let c = Datatype_env.get_constructor_exn cname in
            Type.DatatypeType c.Constructor.constructor_datatype
        | [] -> exceptf "SMT - No cases given in case statement"
      in
      let>- le = f le in
      (* Convert to native *)
      let>- le_native = get_native_of_type constructors_t le in
      (* Encode match cases *)
      let cs, encs =
        cs
        |> List.map (fun (cname, bs, e) ->
               let c = Datatype_env.get_constructor_exn cname in
               let (module V : Variant.Nary) =
                 Datatype_operations.encode_constructor cname
               in
               let pat = PCon (cname, bs) in
               let bts = List.combine bs c.constructor_fields in
               (* TODO: How to handle extra aserts involving bound vars?? *)
               (* Using ite and mapping to undefined values when extra asrts are false cases queries to time out *)
               let _, _, encoded =
                 encode_bound_expr ~encode_expr:encode_logical_expression ~gamma
                   ~llen_lvars ~list_elem_vars bts e
               in
               let encoded = extend_wrap encoded in
               ((pat, encoded.expr), encoded))
        |> List.split
      in
      let fallback = (PVar "_", (extend_wrap undefined_encoding).expr) in
      let>-- _ = encs in
      extended_wrapped (match_datatype le_native.expr (cs @ [ fallback ]))
  | ConstructorApp (cname, les) ->
      let c = Datatype_env.get_constructor_exn cname in
      let (module V : Variant.Nary) =
        Datatype_operations.encode_constructor cname
      in
      let param_types = c.constructor_fields in
      let simple_wrap_or_native = function
        | Some typ -> get_native_of_type typ
        | None -> simple_wrap
      in
      let>-- args = List.map f les in
      let>-- args = List.map2 simple_wrap_or_native param_types args in
      let args = List.map (fun arg -> arg.expr) args in
      let sexp = V.construct args in
      sexp >- DatatypeType c.constructor_datatype

let encode_assertion_top_level
    ~(gamma : typenv)
    ~(llen_lvars : SS.t)
    ~(list_elem_vars : SS.t)
    (a : Expr.t) : Encoding.t =
  try
    encode_logical_expression ~gamma ~llen_lvars ~list_elem_vars
      (Expr.push_in_negations a)
  with e ->
    let s = Printexc.to_string e in
    let msg =
      Fmt.str "Failed to encode %a in gamma %a with error %s\n" Expr.pp a
        pp_typenv gamma s
    in
    let () = L.print_to_all msg in
    raise e

let lvars_only_in_llen (fs : Expr.Set.t) : SS.t =
  let inspector =
    object
      inherit [_] Visitors.iter as super
      val mutable llen_vars = SS.empty
      val mutable other_vars = SS.empty
      method get_diff = SS.diff llen_vars other_vars

      method! visit_expr () e =
        match e with
        | UnOp (UnOp.LstLen, Expr.LVar l) -> llen_vars <- SS.add l llen_vars
        | LVar l -> other_vars <- SS.add l other_vars
        | _ -> super#visit_expr () e
    end
  in
  fs |> Expr.Set.iter (inspector#visit_expr ());
  inspector#get_diff

let lvars_as_list_elements (assertions : Expr.Set.t) : SS.t =
  let collector =
    object (self)
      inherit [_] Visitors.reduce
      inherit Visitors.Utils.ss_monoid

      method! visit_ForAll (exclude, is_in_list) binders f =
        (* Quantified variables need to be excluded *)
        let univ_quant = List.to_seq binders |> Seq.map fst in
        let exclude = Containers.SS.add_seq univ_quant exclude in
        self#visit_expr (exclude, is_in_list) f

      method! visit_Exists (exclude, is_in_list) binders e =
        let exist_quants = List.to_seq binders |> Seq.map fst in
        let exclude = Containers.SS.add_seq exist_quants exclude in
        self#visit_expr (exclude, is_in_list) e

      method! visit_EList (exclude, _) es =
        List.fold_left
          (fun acc e ->
            match e with
            | Expr.LVar x ->
                if not (Containers.SS.mem x exclude) then
                  Containers.SS.add x acc
                else acc
            | _ ->
                let inner = self#visit_expr (exclude, true) e in
                Containers.SS.union acc inner)
          Containers.SS.empty es

      method! visit_LVar (exclude, is_in_list) x =
        if is_in_list && not (Containers.SS.mem x exclude) then
          Containers.SS.singleton x
        else Containers.SS.empty

      method! visit_'label _ (_ : int) = self#zero
      method! visit_'annot _ () = self#zero
    end
  in
  Expr.Set.fold
    (fun f acc ->
      let new_lvars = collector#visit_expr (SS.empty, false) f in
      SS.union new_lvars acc)
    assertions SS.empty

let encode_assertions_needs_handler (fs : Expr.Set.t) (gamma : typenv) :
    sexp list =
  let open Encoding in
  let llen_lvars = lvars_only_in_llen fs in
  let list_elem_vars = lvars_as_list_elements fs in
  let encoded =
    Expr.Set.elements fs
    |> List.map (encode_assertion_top_level ~gamma ~llen_lvars ~list_elem_vars)
  in
  let consts =
    Hashtbl.fold (fun pair () acc -> pair :: acc) (all_consts encoded) []
    |> List.sort Stdlib.compare
    |> List.map (fun (const, typ) -> declare_const const typ)
  in
  let asrts =
    let extra_asrts = List.concat_map (fun e -> e.extra_asrts) encoded in
    let encoded_asrts = List.map (fun e -> e.expr) encoded in
    let facts = List.concat_map (fun e -> e.facts) encoded in
    (* These immutable terms are complete assertions. Keep their first
       occurrence without changing literals, declarations or conjunct order. *)
    let seen = Hashtbl.create 64 in
    extra_asrts @ facts @ encoded_asrts
    |> List.filter (fun assertion ->
         if Hashtbl.mem seen assertion then false
         else (Hashtbl.add seen assertion (); true))
    |> List.map assume
  in
  consts @ asrts

(* Cache concrete prelude commands as well as assertions. User datatype
   declarations are query-dependent: re-running a dynamic declaration builder
   on a cache hit would lose the datatype set discovered during encoding. *)
let encode_assertions (fs : Expr.Set.t) (gamma : typenv) : sexp list * sexp list
    =
  let key = formula_key fs gamma in
  let- () = Formula_cache.find_opt encoding_cache key in
  let encoded, needed =
    with_necessary_definitions @@ fun () ->
    encode_assertions_needs_handler fs gamma
  in
  let declarations = ref [] in
  emit_definitions ~emit:(fun d -> declarations := d :: !declarations) needed;
  let result = (encoded, List.rev !declarations) in
  let () = Formula_cache.replace encoding_cache key result in
  result

(* Opt-in provenance only. Laziness leaves the unset path free of JSON/pretty
   printing; every nested scope restores its predecessor even on an exception. *)
let native_smt_context_scopes : Yojson.Safe.t list ref = ref []

let with_native_smt_context make_context f =
  match Sys.getenv_opt "GILLIAN_NATIVE_SMT_CONTEXT_DIR" with
  | None -> f ()
  | Some _ ->
      let previous = !native_smt_context_scopes in
      native_smt_context_scopes := make_context () :: previous;
      Fun.protect ~finally:(fun () -> native_smt_context_scopes := previous) f

let native_smt_logging_parent () =
  match L.Parent.get () with
  | None ->
      `Assoc [ ("id", `Null); ("status", `String "no-active-parent");
               ("type", `Null); ("content_json", `Null) ]
  | Some id ->
      let report = match L.Parent.get_snapshot () with
        | Some (snapshot_id, type_, content)
          when L.Report_id.equal id snapshot_id -> Some (content, type_)
        | _ -> L.Log_queryer.get_report id
      in
      let fields = match report with
        | None ->
            [ ("status", `String "parent-content-unavailable");
              ("type", `Null); ("content_json", `Null) ]
        | Some (content, type_) ->
            [ ("status", `String
                (if type_ = L.Logging_constants.Content_type.cmd then
                   "current-parent-is-command"
                 else "current-parent-is-not-command; ancestor-unresolved"));
              ("type", `String type_); ("content_json", `String content) ]
      in
      `Assoc (("id", L.Report_id.to_yojson id) :: fields)

module Dump = struct
  let counter = ref 0

  let folder =
    let folder_name = "gillian_smt_queries" in
    let created = ref false in
    let create () =
      created := true;
      try Unix.mkdir folder_name 0o755 with
      | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
      | e -> raise e
    in
    fun () ->
      let () = if not !created then create () in
      folder_name

  let file () =
    let ret = Printf.sprintf "query_%d.smt2" !counter in
    let () = incr counter in
    ret

  let to_file f =
    let () = L.verbose (fun m -> m "Dumping query %d to file" !counter) in
    let name = file () in
    let path = Filename.concat (folder ()) name in
    let c = open_out path in
    let () = f c in
    let () = close_out c in
    name

  let dump fs gamma cmds =
    to_file (fun c ->
        Fmt.pf
          (Format.formatter_of_out_channel c)
          "GIL query:\nFS: %a\nGAMMA: %a\nEncoded as SMT Query:\n%a@?"
          (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp)
          fs pp_typenv gamma
          (Fmt.list ~sep:(Fmt.any "\n") Sexplib.Sexp.pp_mach)
          cmds)
end

(* Opt-in diagnostics of the concrete tuple, never a reconstructed prelude.
   Require the existing dump id and an exclusive fresh sidecar; errors propagate. *)
let capture_native_smt_context ~query ~caller_kind ~timeout_ms ~phase_selection
    ~primary_command_text ~raw_unknown fs gamma encoded_assertions declarations =
  match Sys.getenv_opt "GILLIAN_NATIVE_SMT_CONTEXT_DIR" with
  | None -> ()
  | Some directory ->
      if
        directory = "" || Filename.is_relative directory || query = "none"
        || (Unix.lstat directory).Unix.st_kind <> Unix.S_DIR
      then invalid_arg "Native SMT capture requires an absolute directory and SMT dumping";
      let payload =
        `Assoc
          [
            ("format", `String "gillian-native-smt-context-v1");
            ("query", `String query);
            ("provenance", `Assoc
              [ ("format", `String "gillian-native-smt-query-provenance-v1");
                ("operation_scopes", `List (List.rev !native_smt_context_scopes));
                ("entry", `String
                  (if !native_smt_context_scopes = [] then "direct-smt"
                   else "scoped-fosolver-or-caller"));
                ("logging_parent", native_smt_logging_parent ());
                ("result_status", `String "not-yet-requested");
                ("primary_check_command", `String primary_command_text) ]);
            ("caller", `String caller_kind);
            ("timeout_ms", `String timeout_ms);
            ("phase_selection", `Int phase_selection);
            ("raw_unknown", `Bool raw_unknown);
            ("initial_options", `Assoc (List.map
               (fun (key, value) -> (key, `String value)) z3_config));
            ("original_fs", `String (Fmt.str "%a"
               (Fmt.iter ~sep:Fmt.comma Expr.Set.iter Expr.pp) fs));
            ("original_gamma", `String (Fmt.str "%a" pp_typenv gamma));
            ("declarations", sexps_to_yojson declarations);
            ("encoded_assertions", sexps_to_yojson encoded_assertions);
            ("encoded_assertion_dump", `String (Fmt.str "%a"
               (Fmt.list ~sep:(Fmt.any "\n") Sexplib.Sexp.pp_mach) encoded_assertions));
          ]
      in
      let path = Filename.concat directory (query ^ ".context.json") in
      let channel = open_out_gen
        [ Open_wronly; Open_creat; Open_excl; Open_binary ] 0o600 path in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () ->
          Yojson.Safe.to_channel ~suf:"\n" channel payload;
          flush channel;
          Unix.fsync (Unix.descr_of_out_channel channel));
      (* The closed, file-fsynced sidecar precedes this nondebug event and the
         original declaration/assert/check sequence. No result is fabricated. *)
      let loggable = L.Loggable.make
        (fun fmt json -> Fmt.string fmt (Yojson.Safe.to_string json))
        (fun json -> Ok json) (fun json -> json) payload in
      ignore (L.Specific.normal ~title:"SMT query start" loggable "smt_query_start")

(* We never use the solver incrementally: every query starts by fully
   resetting it. Z3 keeps the options that were set with [set-option] across a
   [(reset)], so there is nothing to re-send here. Working in this one-shot
   mode is important for reliability: when used incrementally (push/pop) Z3 can
   non-deterministically answer [unknown] on queries -- notably ones involving
   the sequence theory -- that it decides immediately in a fresh context. *)
let reset_solver () =
  let () = cmd reset in
  let () = RepeatCache.clear () in
  ()

let exec_sat'
    ~caller_kind
    ~timeout_ms
    ~phase_selection
    ~raw_unknown
    (fs : Expr.Set.t)
    (gamma : typenv) : model option =
  let cost = smt_cost_profile caller_kind in
  let () = ensure_solver_open () in
  let primary_command = primary_check_command_for_phase phase_selection in
  let primary_command_text = primary_check_command_text primary_command in
  let () =
    L.verbose (fun m ->
        m "@[<v 2>About to check SAT of:@\n%a@]@\nwith gamma:@\n@[%a@]\n"
          (Fmt.iter ~sep:(Fmt.any "@\n") Expr.Set.iter Expr.pp)
          fs pp_typenv gamma)
  in
  let () = cost "setup" "none" in
  let () = reset_solver () in
  let () = cmd (set_option ":timeout" timeout_ms) in
  (* Reset retains options; restore the default unless this query explicitly
     requests a different native search policy (e.g. a solver reproducer). *)
  let () =
    cmd (set_option ":smt.phase_selection" (string_of_int phase_selection))
  in
  with_necessary_usr_datatypes @@ fun () ->
  let () = cost "encode" "none" in
  let encoded_assertions, declarations = encode_assertions fs gamma in
  let () = cost "capture" "none" in
  let query = if !Config.dump_smt then
    Dump.dump fs gamma encoded_assertions else "none" in
  let () = capture_native_smt_context ~query ~caller_kind ~timeout_ms
    ~phase_selection ~primary_command_text ~raw_unknown fs gamma encoded_assertions declarations in
  let () = Utils.Owned_prefix_lifecycle.query ~query ~caller:caller_kind in
  let sort_declarations = ref [] in
  let emit (declaration : sexp) =
    (match declaration with
    | List
        (Atom
           ( "declare-datatypes"
           | "declare-datatype"
           | "declare-sort"
           | "define-sort" )
        :: _) -> sort_declarations := declaration :: !sort_declarations
    | _ -> ());
    cmd declaration
  in
  let () = cost "submit" query in
  let () = List.iter emit declarations in
  let () = List.iter cmd encoded_assertions in
  L.verbose (fun fmt -> fmt "Reached SMT.");
  L.normal (fun m ->
    m "SMT_PRIMARY_CHECK_DISPATCH query=%s command=%s" query primary_command_text);
  let current_solver = !solver in
  let () = cost "primary-heartbeat" query in
  let result = primary_check current_solver primary_command in
  let () = cost "postcheck" query in
  (* Join the actual native result to its allocated dump, without changing
     formulas, solver policy or the existing unknown diagnostic/error path. *)
  L.normal (fun m ->
    m "SMT_QUERY_RESULT query=%s caller=%s raw_unknown=%b timeout_ms=%s phase_selection=%d result=%s"
      query caller_kind raw_unknown timeout_ms phase_selection
      (match result with Sat -> "sat" | Unsat -> "unsat" | Unknown -> "unknown"));
  (* Metadata from the same live solver, never another check or reset. Keep
     missing reasons diagnostic-only and retain UNKNOWN's original policy below.
     %S keeps the complete response on one physical log line. *)
  (if result = Unknown then
     let response =
       try Ok (current_solver.raw_command "(get-info :reason-unknown)")
       with
       | (Out_of_memory | Stack_overflow | Sys.Break) as error -> raise error
       | error -> Error (Printexc.to_string error)
     in
     match response with
     | Ok reply ->
         let status = match reply with
           | Sexplib.Sexp.List [Sexplib.Sexp.Atom ":reason-unknown"; _] -> "available"
           | _ -> "unavailable" in
         L.normal (fun m ->
           m "SMT_PRIMARY_UNKNOWN_REASON query=%s status=%s response=%S" query
             status (Sexplib.Sexp.to_string_mach reply))
     | Error error ->
         L.normal (fun m ->
           m "SMT_PRIMARY_UNKNOWN_REASON query=%s status=unavailable error=%S" query error));
  (* Optional unknowns must remain visible without full symbolic-state tracing. *)
  (if result = Unknown then L.normal else L.verbose) (fun m ->
      let r =
        match result with
        | Sat -> "satisfiable"
        | Unsat -> "unsatisfiable"
        | Unknown -> "unknown"
      in
      m "The solver returned: %s" r);
  let ret =
    match result with
    | Unknown ->
        if raw_unknown || !Config.under_approximation then raise SMT_unknown
        else if !Config.Verification.total then
          raise
            (Gillian_result.Exc.Gillian_error
               (OperationError "Incomplete totality proof: SMT returned unknown"))
        else
          let additional_data =
            [
              ("expressions", fs_to_yojson fs);
              ("gamma", typenv_to_yojson gamma);
              ("encoded_assertions", sexps_to_yojson encoded_assertions);
            ]
          in
          raise
            Gillian_result.Exc.(
              internal_error ~additional_data "SMT returned unknown")
    | Sat ->
        Some
          {
            values = get_model !solver;
            sort_declarations = List.rev !sort_declarations;
          }
    | Unsat -> None
  in
  let () = cost "done" query in
  ret

let run_sat
    ~caller_kind
    ?(timeout_ms = List.assoc "timeout" z3_config)
    ~phase_selection
    ~raw_unknown
    (fs : Expr.Set.t)
    (gamma : typenv) : model option =
  try exec_sat' ~caller_kind ~timeout_ms ~phase_selection ~raw_unknown fs gamma
  with UnexpectedSolverResponse response as e ->
    let additional_data =
      [
        ("smt_error", `String (Printexc.to_string e));
        ("smt_response", `String (Sexplib.Sexp.to_string_mach response));
        ("expressions", fs_to_yojson fs);
        ("gamma", typenv_to_yojson gamma);
      ]
    in
    raise Gillian_result.Exc.(internal_error ~additional_data "SMT failure")

let exec_sat ?(caller_kind = "required-complete") ?(phase_selection = 3) fs gamma =
  run_sat ~caller_kind ~phase_selection ~raw_unknown:false fs gamma

(* Optional searches have a smaller budget and never exceed the configured
   required-query limit (zero denotes unlimited). Every query sets its own
   timeout, so an optional attempt cannot shorten a subsequent required check. *)
let optional_timeout cap =
  let configured = int_of_string (List.assoc "timeout" z3_config) in
  string_of_int (if configured = 0 then cap else min cap configured)

(* A bounded natural counter pair may use one optional complete-query witness:
   use 0/2 for a retained strict successor gap, otherwise 0/1, whenever the
   original weak lower bound is present. A strict-only 0 < lower instead tries
   1/3 or 1/2, respectively; these are guesses, never added source premises.
   Positive finite literal lower bounds raise this one candidate to the least
   integral value satisfying those bounds. Preserve the old zero-bound pair
   priority and decline successors outside the exact natural Number range.
   Every original assertion/type remains present. Only a native validated SAT
   model decides; failed hints keep the unchanged path. *)
let nonempty_counter_model fs gamma =
  let vars = Expr.Set.fold (fun e names -> SS.union (Expr.lvars e) names)
    fs SS.empty in
  let numbers = SS.filter (fun name ->
    Hashtbl.find_opt gamma name = Some Type.NumberType) vars in
  let natural name =
    Expr.Set.mem (Expr.UnOp (IsInt, Expr.LVar name)) fs
    && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual,
      Expr.LVar name)) fs in
  let bounded name = Expr.Set.exists (function
    | Expr.BinOp (LVar x, FLessThanEqual, Lit (Num bound)) when x = name ->
        bound >= 0. && bound <= 9007199254740991.
    | _ -> false) fs in
  let ordered_for natural = List.filter_map (function
    | Expr.BinOp (LVar lower, FLessThan, LVar upper)
      when lower <> upper && SS.mem lower numbers && SS.mem upper numbers
        && natural lower
        && Expr.Set.mem (Expr.UnOp (IsInt, Expr.LVar upper)) fs
        && bounded upper ->
          Some (lower, upper)
    | _ -> None) (Expr.Set.elements fs) in
  let strict_natural name =
    Expr.Set.mem (Expr.UnOp (IsInt, Expr.LVar name)) fs
    && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThan, Expr.LVar name)) fs
    && not (Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual,
      Expr.LVar name)) fs) in
  let ordered = ordered_for natural in
  let ordered = if ordered <> [] then ordered else ordered_for strict_natural in
  (* Keep every old direct-pair priority, including ambiguous declines. Only
     then recognize the observed ToInteger upper with its retained equality.
     This selects a full-query model guess; no cast or premise is removed. *)
  let wrapped_for natural = List.filter_map (function
    | Expr.BinOp (LVar lower, FLessThan, (UnOp (ToIntOp, LVar upper) as cast))
      when lower <> upper && SS.mem lower numbers && SS.mem upper numbers
        && natural lower
        && Expr.Set.mem (Expr.UnOp (IsInt, Expr.LVar upper)) fs
        && bounded upper
        && (Expr.Set.mem (Expr.BinOp (cast, Equal, Expr.LVar upper)) fs
            || Expr.Set.mem (Expr.BinOp (Expr.LVar upper, Equal, cast)) fs) ->
          Some (lower, upper)
    | _ -> None) (Expr.Set.elements fs) in
  let ordered = if ordered <> [] then ordered else
    let weak = wrapped_for natural in
    if weak <> [] then weak else wrapped_for strict_natural in
  if not !Config.Verification.total || !Config.under_approximation
     || SS.cardinal numbers < 2 then None else
  match ordered with
  | [] | _ :: _ :: _ -> None
  | [(lower, upper)] ->
      let successor = Expr.BinOp (Expr.LVar lower, FPlus, Expr.num 1.)
      and bound = Expr.LVar upper in
      let upper_value =
        if Expr.Set.mem (Expr.BinOp (successor, FLessThan, bound)) fs
           || (Expr.Set.mem (Expr.BinOp (successor, FLessThanEqual, bound)) fs
               && (Expr.Set.mem (Expr.UnOp (Not, BinOp (successor, Equal, bound))) fs
                   || Expr.Set.mem (Expr.UnOp (Not, BinOp (bound, Equal, successor))) fs))
        then 2. else 1. in
      let lower_value, upper_value =
        if Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual,
          Expr.LVar lower)) fs then 0., upper_value
        else 1., upper_value +. 1. in
      let span = upper_value -. lower_value in
      let lower_value = Expr.Set.fold (fun formula value -> match formula with
        | Expr.BinOp (Lit (Num bound), ((FLessThan | FLessThanEqual) as op), LVar x)
          when x = lower && Float.is_finite bound && bound > 0. ->
            max value (if op = FLessThan then floor bound +. 1. else ceil bound)
        | _ -> value) fs lower_value in
      let upper_value = lower_value +. span in
      if not (Float.is_finite lower_value && lower_value >= 0.
        && upper_value > lower_value && upper_value <= 9007199254740991.)
      then None else
      let query = List.fold_left (fun query (name, value) -> Expr.Set.add
        (Expr.BinOp (Expr.LVar name, ValueEqual, Expr.num value)) query)
        fs [lower, lower_value; upper, upper_value] in
      if Expr.Set.equal query fs then None else
      try run_sat ~caller_kind:"optional-nonempty-counter" ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
          ~raw_unknown:true query gamma
      with SMT_unknown -> None

(* A same-value natural counter alias can make a feasible optional query
   expensive. Try one complete native model first; the two literal hints are
   guesses, never symbolic facts. Only validated SAT decides the original
   query. Failed hints preserve the unchanged unseeded search below. *)
let aliased_counter_model fs gamma =
  let vars = Expr.Set.fold (fun e names -> SS.union (Expr.lvars e) names)
    fs SS.empty in
  let number name = Hashtbl.find_opt gamma name = Some Type.NumberType in
  let natural name =
    Expr.Set.mem (Expr.UnOp (IsInt, Expr.LVar name)) fs
    && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual,
      Expr.LVar name)) fs in
  let bounded name = Expr.Set.exists (function
    | Expr.BinOp (LVar x, FLessThanEqual, Lit (Num bound)) when x = name ->
        bound >= 0. && bound <= 9007199254740991.
    | _ -> false) fs in
  let alias = Expr.Set.exists (function
    | Expr.BinOp (LVar x, Equal, LVar y) when x <> y ->
        natural x && natural y && (bounded x || bounded y)
    | _ -> false) fs in
  if not !Config.Verification.total || !Config.under_approximation
     || SS.cardinal vars <> 2 || not (SS.for_all number vars) || not alias
  then None else
  let query = SS.fold (fun name query -> Expr.Set.add
    (Expr.BinOp (Expr.LVar name, ValueEqual, Expr.num 1.)) query) vars fs in
  if Expr.Set.equal query fs then None else
  try run_sat ~caller_kind:"optional-aliased-counter" ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
      ~raw_unknown:true query gamma
  with SMT_unknown -> None

(* Keep275 q474 is a feasible focused counterquery, not a slice theorem.
   Guess only structurally derived zero/one counter roles and an empty prefix
   in the complete original frame. Only actual native SAT returns a model;
   failed hints preserve every existing timed unseeded query and error. *)
let prefix_length_counter_model fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None else
  let expressions = Expr.Set.elements fs in
  let vars = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
  let numbers = SS.filter (fun name ->
    Hashtbl.find_opt gamma name = Some Type.NumberType) vars in
  let linked a b = Expr.Set.exists (function
    | Expr.BinOp (left, (Equal | ValueEqual), right) ->
        (Expr.equal left a && Expr.equal right b)
        || (Expr.equal right a && Expr.equal left b)
    | _ -> false) fs in
  let select prefix_length successor = match prefix_length, successor with
    | Expr.UnOp (LstLen, (LVar prefix as values)),
      Expr.UnOp (NumToInt, BinOp ((LVar lower as counter), FPlus, Lit (Num step)))
      when step = 1. && SS.cardinal numbers = 3 && SS.mem lower numbers
        && Hashtbl.find_opt gamma prefix = Some Type.ListType ->
        let count = Expr.UnOp (NumToInt, counter) in
        let natural = Expr.Set.mem (Expr.UnOp (IsInt, counter)) fs
          && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual, counter)) fs in
        let bounded = Expr.Set.exists (function
          | Expr.BinOp (LVar x, FLessThanEqual, Lit (Num limit)) when x = lower ->
              limit >= 0. && limit <= 4294967295.
          | _ -> false) fs in
        if not (natural && bounded && linked count prefix_length
          && linked successor (Expr.BinOp (Expr.int 1, IPlus, count))) then None else
        List.find_map (function
          | Expr.BinOp (LVar k, FLessThan, LVar upper)
            when k = lower && upper <> lower && SS.mem upper numbers ->
              let position = SS.choose (SS.remove upper (SS.remove lower numbers)) in
              if Expr.Set.mem (Expr.BinOp (Expr.LVar position, FLessThanEqual, counter)) fs
              then Some (lower,upper,position,values) else None
          | _ -> None) expressions
    | _ -> None in
  let shape = List.find_map (function
    | Expr.UnOp (Not, BinOp (left, (Equal | ValueEqual), right)) ->
        (match select left right with Some _ as roles -> roles
         | None -> select right left)
    | _ -> None) expressions in
  match shape with None -> None | Some (lower,upper,position,prefix) ->
  let query = List.fold_left (fun acc (role,value) -> Expr.Set.add
      (Expr.BinOp (role, ValueEqual, value)) acc) fs
    [Expr.LVar lower,Expr.num 0.; Expr.LVar upper,Expr.num 1.;
     Expr.LVar position,Expr.num 0.; prefix,Expr.EList []] in
  if Expr.Set.equal query fs then None else
  try run_sat ~caller_kind:"optional-prefix-length-counter"
      ~timeout_ms:(optional_timeout 1000) ~phase_selection:3 ~raw_unknown:true query gamma
  with SMT_unknown -> None

(* This is only a sufficient UNSAT check, not a satisfiability decision.
   Native unknown is inconclusive; model/encoding/solver errors still propagate. *)
let proves_unsat ?(caller_kind = "optional-unsat") (fs : Expr.Set.t) (gamma : typenv) : bool =
  let key = formula_key fs gamma in
  match Formula_cache.find_opt sat_cache key with
  | Some result -> Option.is_none result
  | None when Formula_cache.mem inconclusive_prechecks key -> false
  | None -> (
      try
        let result =
          match nonempty_counter_model fs gamma with
          | Some _ as witness -> witness
          | None -> (match aliased_counter_model fs gamma with
            | Some _ as witness -> witness
            | None -> (match prefix_length_counter_model fs gamma with
              | Some _ as witness -> witness
              | None -> run_sat ~caller_kind ~timeout_ms:(optional_timeout 5000) ~phase_selection:3
                  ~raw_unknown:true fs gamma))
        in
        Formula_cache.replace sat_cache key result;
        Option.is_none result
      with SMT_unknown ->
        Formula_cache.replace inconclusive_prechecks key ();
        false)

(* A suffix-only, binder-free compiler copy. The caller retains its original
   frame and caches; a model of this copy is never returned or published. *)
let suffix_alpha_copy full_fs selected gamma roles =
  let preferred_targets = [ "#prefix"; "#dhTailValues"; "#dhHead"; "#k" ] in
  let bindings table = Hashtbl.to_seq table |> List.of_seq |> List.sort Stdlib.compare in
  let originals = List.map fst roles in
  let names = SS.of_list originals in
  let encoded_names xs = SS.of_list (List.map sanitize_identifier xs) in
  let gamma_before = bindings gamma in
  let gamma_names = List.map fst gamma_before in
  (* A simultaneous copy may permute or retain mapped source names. Only
     unmapped Gamma bindings must remain disjoint from the four targets. *)
  let unmapped_names = List.filter (fun name -> not (SS.mem name names)) gamma_names in
  let unmapped_ids = encoded_names unmapped_names in
  let preferred_clashes = SS.inter (encoded_names preferred_targets) unmapped_ids in
  (* Only an occupied preferred head admits this one alternate. Every other
     collision, including an occupied alternate, retains the original fallback. *)
  let targets = if SS.equal preferred_clashes (SS.singleton (sanitize_identifier "#dhHead"))
    then [ "#prefix"; "#dhTailValues"; "#s05_suffix_role_head"; "#k" ]
    else preferred_targets in
  let target_ids = encoded_names targets in
  let source_ids = encoded_names originals in
  let reject reason =
    L.normal (fun m -> m "SUFFIX_ALPHA_COPY_INELIGIBLE reason=%s" reason); false in
  let rec safe = function
    | Expr.LVar name -> SS.mem name names
    | Expr.Lit (Int _ | Num _) -> true
    | Expr.UnOp ((Not | NumToInt | LstLen | IsInt), e) -> safe e
    | Expr.BinOp (a, (Equal | ValueEqual | FLessThanEqual | FPlus | IPlus | ITimes), b) -> safe a && safe b
    | Expr.LstSub (a,b,c) -> safe a && safe b && safe c
    | Expr.NOp (LstCat, es) | Expr.EList es -> List.for_all safe es
    | _ -> false in
  let used = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) selected SS.empty in
  if List.length roles <> 4 || SS.cardinal names <> 4
     || List.map snd roles <> [Type.ListType;Type.ListType;Type.Utf16Type;Type.NumberType]
     || not (List.for_all (fun (name,typ) -> Hashtbl.find_opt gamma name = Some typ) roles)
     || Expr.Set.cardinal selected <> 6 || not (Expr.Set.subset selected full_fs)
     || Expr.Set.cardinal selected >= Expr.Set.cardinal full_fs
     || not (SS.equal used names && Expr.Set.for_all safe selected)
  then reject "shape-or-alias" else
  (* The matched fragment emits no binders/functions with this logical-variable
     prefix. Reject nonstandard identifiers rather than guessing their scope. *)
  let identifier name = String.starts_with ~prefix:"$$" name
    && String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' | '$' -> true | _ -> false) name in
  if not (SS.for_all identifier (SS.union source_ids target_ids))
     || SS.cardinal source_ids <> 4 || SS.cardinal target_ids <> 4
     || SS.cardinal (encoded_names gamma_names) <> List.length gamma_names
     || not (SS.is_empty (SS.inter target_ids unmapped_ids))
  then reject "encoded-name-collision" else
  let mapping = List.combine originals targets in
  let inverse = List.map (fun (a,b) -> b,a) mapping in
  let rename map name = Option.value ~default:name (List.assoc_opt name map) in
  let map_expr map e = Expr.map_opt (function
    | Expr.LVar name -> Some (Expr.LVar (rename map name)),false
    | e -> Some e,true) None e |> Option.get in
  let map_fs map fs = Expr.Set.fold (fun e acc -> Expr.Set.add (map_expr map e) acc) fs Expr.Set.empty in
  let map_gamma map table =
    let copied = Hashtbl.create (Hashtbl.length table) in
    Hashtbl.iter (fun name typ -> Hashtbl.add copied (rename map name) typ) table; copied in
  let copied = map_fs mapping selected and copied_gamma = map_gamma mapping gamma in
  if Expr.Set.cardinal copied <> 6 || Hashtbl.length copied_gamma <> Hashtbl.length gamma
     || SS.cardinal (encoded_names (List.map fst (bindings copied_gamma))) <> Hashtbl.length copied_gamma
     || not (Expr.Set.equal (map_fs inverse copied) selected)
     || bindings (map_gamma inverse copied_gamma) <> gamma_before
  then reject "inverse" else
  let commands, prelude = with_necessary_usr_datatypes (fun () -> encode_assertions selected gamma) in
  let copied_commands, copied_prelude = with_necessary_usr_datatypes (fun () -> encode_assertions copied copied_gamma) in
  let rec atoms = function
    | Sexplib.Sexp.Atom a -> SS.singleton a
    | Sexplib.Sexp.List xs -> List.fold_left (fun acc x -> SS.union acc (atoms x)) SS.empty xs in
  let prelude_atoms = List.fold_left (fun acc x -> SS.union acc (atoms x)) SS.empty (prelude @ copied_prelude) in
  let rec binder_free = function
    | Sexplib.Sexp.List (Sexplib.Sexp.Atom ("forall" | "exists" | "let") :: _) -> false
    | Sexplib.Sexp.List xs -> List.for_all binder_free xs
    | Sexplib.Sexp.Atom _ -> true in
  let declaration_names xs = List.filter_map (function
    | Sexplib.Sexp.List [Sexplib.Sexp.Atom "declare-const";Sexplib.Sexp.Atom name;_] -> Some name
    | _ -> None) xs |> SS.of_list in
  let encoded_mapping = List.map (fun (a,b) -> sanitize_identifier a,sanitize_identifier b) mapping in
  let rec rename_sexp = function
    | Sexplib.Sexp.Atom a -> Sexplib.Sexp.Atom (rename encoded_mapping a)
    | Sexplib.Sexp.List xs -> Sexplib.Sexp.List (List.map rename_sexp xs) in
  if not (SS.is_empty (SS.inter prelude_atoms (SS.union source_ids target_ids)))
  then reject "prelude-collision" else
  if not (List.for_all binder_free (commands @ copied_commands))
     || not (SS.equal (declaration_names commands) source_ids)
     || not (SS.equal (declaration_names copied_commands) target_ids)
     || prelude <> copied_prelude
     || List.sort Stdlib.compare (List.map rename_sexp commands) <> List.sort Stdlib.compare copied_commands
  then reject "encoded-correspondence" else
  let () = L.normal (fun m -> m "SUFFIX_ALPHA_COPY_MAP %s"
    (String.concat ";" (List.map (fun (a,b) -> a ^ "->" ^ b) mapping))) in
  try
    let result = run_sat ~caller_kind:"optional-symbolic-suffix-alpha-copy"
      ~timeout_ms:(optional_timeout 5000) ~phase_selection:3 ~raw_unknown:true copied copied_gamma in
    if bindings gamma <> gamma_before then exceptf "suffix alpha copy changed caller Gamma";
    Option.is_none result
  with SMT_unknown -> false

(* Search for an existential witness using extra equalities, without changing
   the symbolic state. Only a native, validated SAT model of the complete
   strengthened query can decide the original query. UNSAT/unknown says nothing
   about the original inputs and must fall back. Keep this optimization limited
   to total-mode feasibility with multiple UTF-16/Number variables, a direct
   rounded-length equality, or the retained finite predecessor/ListNth shape.
   The latter admits numeric zero, not an implied bitwise predecessor identity. *)
let seeded_model fs gamma =
  let vars =
    Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty
  in
  let count_type typ =
    SS.cardinal (SS.filter (fun x -> Hashtbl.find_opt gamma x = Some typ) vars)
  in
  let try_seed query =
    (* Reject only new finite Number guesses contradicted by an original
       direct literal constraint. This is candidate pruning, never an UNSAT
       decision about fs. Numeric comparison deliberately identifies +/-0;
       unsupported expressions and nonfinite literals remain unanalysed. *)
    let violates left (op : BinOp.t) right = match op with
      | FLessThan -> not (left < right)
      | FLessThanEqual -> not (left <= right)
      | Equal | ValueEqual -> left <> right
      | _ -> false in
    let conflicting = Expr.Set.exists (function
      | Expr.BinOp (LVar name, (Equal | ValueEqual), Lit (Num value))
      | Expr.BinOp (Lit (Num value), (Equal | ValueEqual), LVar name)
        when Hashtbl.find_opt gamma name = Some Type.NumberType
          && Float.is_finite value ->
          Expr.Set.exists (function
            | Expr.BinOp (LVar x, op, Lit (Num bound))
              when x = name && Float.is_finite bound ->
                violates value op bound
            | Expr.BinOp (Lit (Num bound), op, LVar x)
              when x = name && Float.is_finite bound ->
                violates bound op value
            | _ -> false) fs
      | _ -> false) (Expr.Set.diff query fs) in
    if conflicting then None else try
      run_sat ~caller_kind:"optional-seeded-model" ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
        ~raw_unknown:true query gamma
    with SMT_unknown -> None
  in
  let literal_candidate () =
    (* This existing numeric search does not require a second counter or a
       UTF16 loop. Keep the content/rounded-length guard and passive raw upper
       bounds unchanged. One complete candidate may succeed only through native
       validated SAT; guesses never become state facts. *)
    let contents =
      object
        inherit [_] Visitors.iter as super
        val mutable seen = false
        method seen = seen
        method! visit_expr () e =
          (match e with
          | BinOp (_, (Utf16Nth | Utf16CodeUnit | Utf16Cat | Utf16Less
                      | StrNth | StrCat | StrLess), _)
          | UnOp ((Utf16Len | Utf16Trim | Utf16ToNumber | NumberToUtf16
                  | StrLen | ToNumberOp | ToStringOp | StrToBytes), _) ->
              seen <- true
          | _ -> ());
          super#visit_expr () e
      end
    in
    Expr.Set.iter (function
      | Expr.BinOp (UnOp (Utf16Len, LVar string), ILessThanEqual,
          Lit (Int bound))
        when Hashtbl.find_opt gamma string = Some Type.Utf16Type
          && Z.sign bound >= 0 -> ()
      | expression -> contents#visit_expr () expression) fs;
    if contents#seen then None else
    let number x = Hashtbl.find_opt gamma x = Some Type.NumberType in
    let literal_values = Expr.Set.fold (fun e acc -> match e with
      | BinOp (LVar x, (Equal | ValueEqual), Lit (Num value))
      | BinOp (Lit (Num value), (Equal | ValueEqual), LVar x)
        when number x && not (List.mem_assoc x acc) -> (x,value)::acc
      | _ -> acc) fs [] in
    let root_guess x = Expr.Set.fold (fun e value ->
      let bound lower strict =
        if lower >= 0. && lower < 8. then
          max value (if strict then floor lower +. 1. else ceil lower)
        else value in
      match e with
      | BinOp (Lit (Num lower), FLessThan, LVar name) when name = x ->
          bound lower true
      | BinOp (Lit (Num lower), FLessThanEqual, LVar name)
      | UnOp (Not, BinOp (LVar name, FLessThan, Lit (Num lower)))
        when name = x -> bound lower false
      | _ -> value) fs 0. in
    let initial = SS.fold (fun x acc ->
      let guess = root_guess x in
      if number x && guess > 0. && not (List.mem_assoc x acc)
      then (x,guess)::acc else acc) vars literal_values in
    if List.length initial = List.length literal_values then None else
    let value guesses = function
      | Expr.LVar x -> List.assoc_opt x guesses
      | Lit (Num n) -> Some n
      | BinOp (LVar x, (FPlus | FMinus as op), Lit (Num 1.)) ->
          Option.map (fun n -> if op = FPlus then n +. 1. else n -. 1.)
            (List.assoc_opt x guesses)
      | _ -> None in
    let assign grow x guess acc =
      if not (number x) || List.mem_assoc x literal_values then acc
      else match List.assoc_opt x acc with
      | None -> (x,guess)::acc
      | Some old when grow && guess > old ->
          List.map (fun (name,n) -> name,(if name = x then guess else n)) acc
      | _ -> acc in
    let step guesses = Expr.Set.fold (fun e acc ->
      let equal left right acc = match left,value acc right with
        | Expr.LVar x,Some n -> assign true x n acc | _ -> acc in
      match e with
      | BinOp (left,(Equal | ValueEqual),right) ->
          equal right left (equal left right acc)
      | BinOp (lower,(FLessThan | FLessThanEqual as op),LVar upper) ->
          (match value acc lower with
          | Some n -> assign true upper
              (if op = FLessThan then floor n +. 1. else n) acc
          | None -> acc)
      | _ -> acc) fs guesses in
    (* Fixed rounds bound cyclic inequalities deterministically. No fixed
       point, feasibility result, or arithmetic law is assumed. *)
    let rec propagate remaining guesses =
      if remaining = 0 then guesses
      else propagate (remaining-1) (step guesses) in
    let guesses = propagate (SS.cardinal vars) initial in
    let query = List.fold_left (fun acc (x,n) -> Expr.Set.add
      (Expr.BinOp (LVar x,ValueEqual,Expr.num n)) acc) fs guesses in
    try_seed query
  in
  let length_pair number string =
    (* Entailment may leave the linked Number wrapped rather than retaining
       a gamma entry. The original equality still stays in the complete query;
       eligibility need not assume or add its type to the symbolic state. *)
    (match Hashtbl.find_opt gamma number with
    | None | Some Type.NumberType -> true
    | _ -> false)
    && Hashtbl.find_opt gamma string = Some Type.Utf16Type
  in
  (* Reduction can inline the length alias before a branch query. Recognise
     the same rounded-length observation in a direct numeric comparison; this
     only selects an optional search, never adds a symbolic-state fact. *)
  let rounded_string expression acc =
    match expression with
    | Expr.UnOp (IntToNum, UnOp (Utf16Len, LVar string))
      when Hashtbl.find_opt gamma string = Some Type.Utf16Type ->
        SS.add string acc
    | _ -> acc
  in
  let rec compared_strings = function
    | Expr.UnOp (Not, formula) -> compared_strings formula
    | BinOp (left, (FLessThan | FLessThanEqual), right) ->
        rounded_string right (rounded_string left SS.empty)
    | _ -> SS.empty
  in
  let length_strings =
    Expr.Set.fold
      (fun assertion acc ->
        match assertion with
        | BinOp
            ( LVar number,
              (Equal | ValueEqual),
              UnOp (IntToNum, UnOp (Utf16Len, LVar string)) )
        | BinOp
            ( UnOp (IntToNum, UnOp (Utf16Len, LVar string)),
              (Equal | ValueEqual),
              LVar number )
          when length_pair number string -> SS.add string acc
        | _ -> SS.union (compared_strings assertion) acc)
      fs SS.empty
  in
  if not !Config.Verification.total then None
  else if not ((count_type Type.Utf16Type >= 2 && count_type Type.NumberType >= 2)
               || not (SS.is_empty length_strings))
  then literal_candidate ()
  else
    let seeded =
      SS.fold
        (fun x acc ->
          let value =
            match Hashtbl.find_opt gamma x with
            | Some Type.Utf16Type ->
                Some
                  (Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical "")))
            | Some Type.NumberType -> Some (Expr.num 0.)
            | _ -> None
          in
          match value with
          | None -> acc
          | Some value ->
              Expr.Set.add (Expr.BinOp (Expr.LVar x, Equal, value)) acc)
        vars fs
    in
    match try_seed seeded with
    | Some _ as witness -> witness
    | None when not (SS.is_empty length_strings) -> (
        (* Empty/zero guesses miss branches needing one or two code units.
           Leave contents and every Number variable free, and construct each
           attempt from the original complete formula. Only validated SAT can
           succeed; failed guesses still fall back without changing state. *)
        let with_length length =
          SS.fold
            (fun string acc ->
              Expr.Set.add
                (Expr.BinOp
                   ( Expr.UnOp (Utf16Len, Expr.LVar string),
                     Equal,
                     Expr.int length ))
                acc)
            length_strings fs
        in
        (* Try a small concrete position before leaving Number indices free.
           Both are complete-query witness searches. This ordering avoids a
           native solver crash on a retained free-position length-two query;
           failed guesses still reach all original attempts and required checks.
           The singleton attempt covers a last-code-unit branch whose invariant
           aliases otherwise make free-position feasibility fragile. *)
        let indices =
          object
            inherit [_] Visitors.iter as super
            val mutable names = SS.empty
            method names = names

            method! visit_expr () e =
              (match e with
              | BinOp (LVar string, (Utf16Nth | Utf16CodeUnit), index)
                when SS.mem string length_strings ->
                  names <- SS.union names (Expr.lvars index)
              | _ -> ());
              super#visit_expr () e
          end
        in
        Expr.Set.iter (indices#visit_expr ()) fs;
        let numbers =
          SS.filter
            (fun x -> Hashtbl.find_opt gamma x = Some Type.NumberType)
            indices#names
        in
        (* A free counter can still make a position/length witness expensive.
           Also try zero for Number variables not equated to another expression.
           This is only a guess: every original assertion remains in the query,
           and failed guesses fall back to the existing searches and budget. *)
        let defined =
          Expr.Set.fold
            (fun e names ->
              let add left right names =
                match left with
                | Expr.LVar x when not (Expr.equal left right) -> SS.add x names
                | _ -> names
              in
              match e with
              | Expr.BinOp (left, (Equal | ValueEqual), right) ->
                  add right left (add left right names)
              | _ -> names)
            fs SS.empty
        in
        let roots =
          SS.filter
            (fun x ->
              Hashtbl.find_opt gamma x = Some Type.NumberType
              && (not (SS.mem x defined))
              && not (SS.mem x numbers))
            vars
        in
        let with_zeros names query =
          SS.fold
            (fun x acc ->
              Expr.Set.add
                (Expr.BinOp (Expr.LVar x, ValueEqual, Expr.num 0.))
                acc)
            names query
        in
        (* Propagation only proposes additional witness values. It neither
           proves an arithmetic identity nor changes the symbolic state. *)
        let rec extend_values guesses =
          let next = Expr.Set.fold (fun e acc ->
            let add left right acc = match left, right with
              | Expr.LVar x, Expr.BinOp (LVar from, (FPlus | FMinus as op), Lit (Num 1.))
                when Hashtbl.find_opt gamma x = Some Type.NumberType
                     && not (List.mem_assoc x acc) ->
                (match List.assoc_opt from acc with
                 | Some value -> (x, (if op = FPlus then value +. 1.
                                      else value -. 1.)) :: acc
                 | None -> acc)
              | _ -> acc in
            match e with
            | BinOp (left, (Equal | ValueEqual), right) ->
                add right left (add left right acc)
            | _ -> acc) fs guesses in
          if List.length next = List.length guesses then next else extend_values next
        in
        let seed_values initial query =
          let initial = Expr.Set.fold (fun e acc -> match e with
            | BinOp (LVar x, (Equal | ValueEqual), Lit (Num value))
            | BinOp (Lit (Num value), (Equal | ValueEqual), LVar x)
              when Hashtbl.find_opt gamma x = Some Type.NumberType
                   && not (List.mem_assoc x acc) -> (x, value) :: acc
            | _ -> acc) fs initial in
          List.fold_left (fun acc (x, value) -> Expr.Set.add
            (Expr.BinOp (LVar x, ValueEqual, Expr.num value)) acc)
            query (extend_values initial)
        in
        (* Loop feasibility can need a concrete adjacent-index counter even
           in queries without UTF-16 content operations. Keep the existing
           character-position search unchanged for content queries. Otherwise
           try zero and one with length one;
           retain the complete formula and accept only a validated native model.
           Failure leaves every existing search and the required query intact. *)
        let advancing =
          object
            inherit [_] Visitors.iter as super
            val mutable names = SS.empty
            val mutable contents = false
            method names = names
            method observes_contents = contents
            method! visit_expr () e =
              (match e with
              | BinOp (_, (Utf16Nth | Utf16CodeUnit | Utf16Cat | Utf16Less), _)
              | UnOp (Utf16ToNumber, _) -> contents <- true
              | BinOp (LVar x, (FPlus | FMinus), Lit (Num 1.))
                when Hashtbl.find_opt gamma x = Some Type.NumberType ->
                  names <- SS.add x names
              | _ -> ());
              super#visit_expr () e
          end
        in
        Expr.Set.iter (advancing#visit_expr ()) fs;
        (* A carried loop limit need not share the advancing counter's value.
           Guess distinct roots and their adjacent derived values, retaining
           every original equation. A native validated model, under the same
           optional budget, is the only success; failed guesses still fall back. *)
        let counter_roots = SS.inter roots advancing#names in
        let carried_roots = SS.diff roots advancing#names in
        let carried =
          if advancing#observes_contents || SS.is_empty carried_roots then None
          else
            (* A chain can begin at an original literal-bound counter as well
               as a free root. Those bindings remain in the full formula; here
               they only guide a candidate model. *)
            let literal_values = Expr.Set.fold (fun e acc -> match e with
              | BinOp (LVar x, (Equal | ValueEqual), Lit (Num value))
              | BinOp (Lit (Num value), (Equal | ValueEqual), LVar x)
                when Hashtbl.find_opt gamma x = Some Type.NumberType
                     && not (List.mem_assoc x acc) -> (x, value) :: acc
              | _ -> acc) fs [] in
            let initial = SS.fold (fun x acc -> (x, 0.) :: acc) counter_roots
              (SS.fold (fun x acc -> (x, 1.) :: acc) carried_roots literal_values) in
            let counter_initial = SS.fold (fun x acc -> (x, 0.) :: acc)
              counter_roots literal_values in
            if List.length (extend_values counter_initial) < List.length counter_initial + 2
            then None else
            (* A deeper adjacent chain may require distinct carried limits.
               Raise only guessed free limits to observed lower guesses. This
               never establishes a fact; all original bounds remain checked. *)
            let rec carry_limits guesses =
              let values = extend_values guesses in
              let next = Expr.Set.fold (fun e acc -> match e with
                | Expr.BinOp (LVar lower, FLessThanEqual, LVar upper)
                  when SS.mem upper carried_roots ->
                  (match List.assoc_opt lower values, List.assoc_opt upper acc with
                   | Some value, Some old when value > old ->
                       List.map (fun (name, guess) ->
                         (name, if name = upper then value else guess)) acc
                   | _ -> acc)
                | _ -> acc) fs values in
              if next = values then values else carry_limits next
            in
            let values = carry_limits initial in
            (* Keep allocation bounded even when unrelated Number values are
               large. Failed short guesses still reach the existing fallback. *)
            let length = List.fold_left (fun bound (_, value) ->
              if value >= 0. && value <= 8. && floor value = value
              then max bound (int_of_float value) else bound) 2 values in
            let value = Utils.Utf16.of_canonical (Utils.Utf16.of_code_units
              (List.init length (fun _ -> 0x41))) in
            let query = SS.fold
              (fun string acc -> Expr.Set.add
                (Expr.BinOp (LVar string, Equal,
                  Lit (Utf16String value))) acc) length_strings fs in
            let query = seed_values values query in
            try_seed query
        in
        (* Some complete pure/list branch queries require a free counter
           beyond the existing zero/one guesses. Literal lower bounds select
           a small candidate only; all original assertions remain checked. *)
        let root_guess x = Expr.Set.fold (fun e value ->
          let bound lower strict =
            if lower >= 0. && lower < 8. then
              max value (if strict then floor lower +. 1. else ceil lower)
            else value in
          match e with
          | BinOp (Lit (Num lower), FLessThan, LVar name) when name = x ->
              bound lower true
          | BinOp (Lit (Num lower), FLessThanEqual, LVar name)
          | UnOp (Not, BinOp (LVar name, FLessThan, Lit (Num lower)))
            when name = x -> bound lower false
          | _ -> value) fs 0. in
        let bounded =
          if advancing#observes_contents
             || not (SS.exists (fun x -> root_guess x > 1.) advancing#names)
          then None else
            (* A self-referential identity is not an assignment, but may
               exclude its counter from the older free-root heuristic. *)
            let guesses = SS.fold (fun x acc -> (x, root_guess x) :: acc)
              (SS.union roots advancing#names) [] in
            let query = SS.fold (fun string acc -> Expr.Set.add
              (Expr.BinOp (LVar string, Equal,
                Lit (Utf16String (Utils.Utf16.of_canonical "A")))) acc)
              length_strings fs in
            try_seed (seed_values guesses query)
        in
        (* Two adjacent units at a fixed zero index can arise during
           predicate recovery. Select a code-unit hint from the observed
           surrogate bounds; every fact remains in the complete SAT query. *)
        let fixed_pair_index string =
          Expr.Set.fold (fun assertion found -> match found with
            | Some _ -> found
            | None ->
              let matches left right = match left, right with
                | Expr.UnOp (IntToNum, UnOp (Utf16Len, LVar observed)),
                  Expr.BinOp (BinOp (LVar index, FPlus, Lit (Num 1.)),
                    FPlus, Lit (Num 1.)) when observed = string ->
                  if Hashtbl.find_opt gamma index = Some Type.NumberType
                    && (Expr.Set.mem (Expr.BinOp (LVar index, Equal, Expr.num 0.)) fs
                        || Expr.Set.mem (Expr.BinOp (Expr.num 0., Equal, LVar index)) fs)
                  then Some index else None
                | _ -> None in
              match assertion with
              | Expr.BinOp (left, (Equal | ValueEqual), right) ->
                  (match matches left right with Some _ as index -> index
                   | None -> matches right left)
              | _ -> None) fs None
        in
        let fixed_pair_strings = SS.filter (fun string ->
          Option.is_some (fixed_pair_index string)) length_strings in
        let unit_hint string position =
          let code = Expr.BinOp (LVar string, Utf16CodeUnit,
            UnOp (ToIntOp, position)) in
          let lower bound = Expr.Set.mem
            (Expr.BinOp (Expr.num bound, FLessThanEqual, code)) fs in
          let upper bound = Expr.Set.mem
            (Expr.BinOp (code, FLessThanEqual, Expr.num bound)) fs in
          if lower 55296. && upper 56319. then 0xd800
          else if lower 56320. && upper 57343. then 0xdc00
          else if lower 55296. || lower 56320. then 0xe000
          else 0x41
        in
        let fixed_pair =
          if SS.is_empty fixed_pair_strings then None else
          let query = SS.fold (fun string acc ->
            let position = Expr.LVar (Option.get (fixed_pair_index string)) in
            let next = Expr.BinOp (position, FPlus, Expr.num 1.) in
            let value = Utils.Utf16.of_canonical (Utils.Utf16.of_code_units
              [unit_hint string position; unit_hint string next]) in
            Expr.Set.add (Expr.BinOp (LVar string, Equal,
              Lit (Utf16String value))) acc) fixed_pair_strings fs in
          let guesses = SS.fold (fun x acc -> (x, 1.) :: acc) roots [] in
          try_seed (seed_values guesses query)
        in
        (* The one-unit shape includes ordinary units and lone high
           surrogates. Select only a hint; all content/range facts and the
           original complete-query validation remain authoritative. *)
        let singleton_index string = List.find_opt (fun index ->
          let pos = Expr.LVar index in
          let rounded = Expr.UnOp (IntToNum, UnOp (Utf16Len, LVar string)) in
          let next = Expr.BinOp (pos, FPlus, Expr.num 1.) in
          let equal left right = List.exists (fun op ->
            Expr.Set.mem (Expr.BinOp (left, op, right)) fs
            || Expr.Set.mem (Expr.BinOp (right, op, left)) fs)
            [ Equal; ValueEqual ] in
          Hashtbl.find_opt gamma index = Some Type.NumberType
          && equal pos (Expr.num 0.) && equal rounded next) (SS.elements vars) in
        let singleton_strings = SS.filter (fun string ->
          Option.is_some (singleton_index string)) length_strings in
        let singleton =
          if SS.is_empty singleton_strings then None else
          let query = SS.fold (fun string acc ->
            let position = Expr.LVar (Option.get (singleton_index string)) in
            let value = Utils.Utf16.of_canonical (Utils.Utf16.of_code_units
              [unit_hint string position]) in
            Expr.Set.add (Expr.BinOp (LVar string, Equal,
              Lit (Utf16String value))) acc) singleton_strings fs in
          let guesses = SS.fold (fun x acc -> (x, 1.) :: acc) roots [] in
          try_seed (seed_values guesses query)
        in
        let stepped =
          match bounded with
          | Some _ as witness -> witness
          | None ->
          match (match singleton with Some _ -> singleton
            | None -> (match fixed_pair with Some _ -> fixed_pair | None -> carried)) with
          | Some _ as witness -> witness
          | None ->
          if advancing#observes_contents || SS.is_empty advancing#names then None
          else
            let try_values names base = List.find_map
              (fun value ->
                let query = SS.fold
                  (fun x acc -> Expr.Set.add
                    (Expr.BinOp (LVar x, ValueEqual, Lit (Num value))) acc)
                  names base in
                try_seed query)
              [ 0.; 1. ] in
            match try_values advancing#names (with_length 1) with
            | Some _ as witness -> witness
            | None ->
                (* Independent loops may need different counter values.
                   Preserve the existing guesses, then use literal-bound values
                   in this optional witness, including the literal zero sign.
                   Original equalities remain; only a validated SAT model wins. *)
                let fixed, base = Expr.Set.fold
                  (fun e (names, query) -> match e with
                   | BinOp (LVar x, (Equal | ValueEqual), Lit (Num value))
                   | BinOp (Lit (Num value), (Equal | ValueEqual), LVar x)
                     when SS.mem x advancing#names ->
                       (SS.add x names, Expr.Set.add
                         (Expr.BinOp (LVar x, ValueEqual, Lit (Num value))) query)
                   | _ -> (names, query)) fs (SS.empty, with_length 1) in
                let remaining = SS.diff advancing#names fixed in
                if SS.is_empty remaining || SS.equal remaining advancing#names
                then None else try_values remaining base
        in
        let positioned =
          match stepped with
          | Some _ as witness -> witness
          | None -> if SS.is_empty numbers then None
          else
            List.find_map
              (fun length ->
                let query = with_zeros numbers (with_length length) in
                let rooted =
                  if SS.is_empty roots then None
                  else try_seed (with_zeros roots query)
                in
                match rooted with
                | Some _ as witness -> witness
                | None -> try_seed query)
              [ 2; 1 ]
        in
        match positioned with
        | Some _ as witness -> witness
        (* Try empty length without fixing derived Number variables; each
           attempt preserves the full query and only a validated SAT model
           succeeds. *)
        | None -> List.find_map (fun n -> try_seed (with_length n)) [ 0; 1; 2 ])
    | None -> literal_candidate ()

(* Rounded-length upper-bound queries can combine expensive sequence and
   floating-point theories. First prove an exact index identity using original
   integrality facts alone. Only native UNSAT permits adding that consequence;
   the required query still includes every original fact. This is a checked cut,
   not an assumed arithmetic law or a branch decision from an incomplete subset. *)
let with_checked_index_identities fs gamma =
  if not !Config.Verification.total then fs
  else
    let indices =
      Expr.Set.fold
        (fun e acc ->
          match e with
          | Expr.BinOp
              ( UnOp (IntToNum, UnOp (Utf16Len, _)),
                FLessThanEqual,
                UnOp (ToIntOp, index) ) -> Expr.Set.add index acc
          | _ -> acc)
        fs Expr.Set.empty
    in
    Expr.Set.fold
      (fun index augmented ->
        let identity = Expr.BinOp (UnOp (ToIntOp, index), ValueEqual, index) in
        let premises =
          Expr.Set.filter
            (function
              | Expr.UnOp (IsInt, e) ->
                  SS.subset (Expr.lvars e) (Expr.lvars index)
                  && SS.subset (Expr.pvars e) (Expr.pvars index)
                  && SS.subset (Expr.locs e) (Expr.locs index)
              | _ -> false)
            fs
        in
        if
          (not (Expr.Set.is_empty premises))
          && proves_unsat ~caller_kind:"optional-checked-index-identity"
               (Expr.Set.add (Expr.UnOp (Not, identity)) premises)
               gamma
        then Expr.Set.add identity augmented
        else augmented)
      indices fs

(* Sufficient native UNSAT precheck before the complete-query witness search.
   When the original expression set is a mixed UTF-16/Number query, a native
   mixed query can crash or take far longer than a pure-numeric query. Before
   paying that cost, we check whether a nonempty PROPER numeric subset of the
   original top-level expressions is itself unsatisfiable. If so, the whole
   conjunction is unsatisfiable (every model of the full conjunction would be a
   model of the subset, which has none), so we return None without touching the
   solver. A numeric SAT or unknown answer on the subset CANNOT establish the
   feasibility of the original query, so those cases fall through to the
   pre-existing complete-query path unchanged. Only total-mode queries that
   actually reference a UTF-16 variable are eligible, because pure-numeric
   queries already use the cheaper path and the crash risk is specific to
   mixed UTF-16/Number formulas. *)
(* A failed Number rank can be a disjunction of up to three negated
   arithmetic conditions. Prove each branch impossible over original numeric
   premises. Boolean case splitting and premise omission add no arithmetic law;
   every branch still needs native UNSAT with unchanged binary64 semantics. *)
let number_rank_cases fs gamma =
  let rec number = function
    | Expr.Lit (Num _) -> true
    | LVar x -> Hashtbl.find_opt gamma x = Some Type.NumberType
    | BinOp (a, (FPlus | FMinus), b) -> number a && number b
    | _ -> false in
  let atom = function
    | Expr.UnOp (IsInt, e) -> number e
    | BinOp (a, (Equal | ValueEqual | FLessThan | FLessThanEqual), b) ->
        number a && number b
    | _ -> false in
  let rec difference = function
    | Expr.BinOp (_, FMinus, _) -> true
    | BinOp (a, _, b) -> difference a || difference b
    | UnOp (_, e) -> difference e
    | _ -> false in
  let rec alternatives = function
    | Expr.BinOp (a, Or, b) ->
        (match alternatives a, alternatives b with
         | Some a, Some b when List.length a + List.length b <= 3 -> Some (a @ b)
         | _ -> None)
    | (UnOp (Not, e) as failed) when atom e && difference e -> Some [ failed ]
    | _ -> None in
  let premises = Expr.Set.filter (function
    | Expr.UnOp (Not, e) -> atom e
    | e -> atom e) fs in
  if Expr.Set.is_empty premises then None else
  List.find_map (fun e -> match alternatives e with
    | Some cases when List.length cases >= 2
        && Expr.Set.cardinal premises + 1 < Expr.Set.cardinal fs ->
        Some (List.map (fun failed -> Expr.Set.add failed premises) cases)
    | _ -> None) (Expr.Set.elements fs)

let numeric_unsat_precheck (fs : Expr.Set.t) (gamma : typenv) : bool =
  if not !Config.Verification.total then false
  else
    (* Eligible only when at least one original expression references an
       existing UTF-16 variable; this is the mixed-query case. *)
    let has_utf16_ref =
      Expr.Set.exists
        (fun e ->
          SS.exists
            (fun x -> Hashtbl.find_opt gamma x = Some Type.Utf16Type)
            (Expr.lvars e))
        fs
    in
    let rank_impossible = has_utf16_ref &&
      (match number_rank_cases fs gamma with
       | Some cases -> List.for_all (fun branch -> proves_unsat ~caller_kind:"optional-numeric-rank-case" branch gamma) cases
       | None -> false) in
    if rank_impossible then true
    else if not has_utf16_ref then false
    else
      (* A conservative recursive numeric-term recognizer over the original
         gamma: a term is numeric iff it is a numeric literal, a variable of
         existing NumberType, or the FPlus of two numeric terms. No rewriting,
         no new types, no facts added. *)
      let is_numeric e =
        let rec is_num = function
          | Expr.Lit (Num _) -> true
          | Expr.LVar x -> Hashtbl.find_opt gamma x = Some Type.NumberType
          | Expr.BinOp (a, FPlus, b) -> is_num a && is_num b
          | _ -> false
        in
        is_num e
      in
      (* Keep exactly the top-level atoms that are pure numeric comparisons:
         is_int of a numeric term, or a numeric==numeric / numeric<=numeric
         binary comparison. Every other atom is dropped; retained ASTs are
         unchanged. This narrow grammar is decided by native binary64
         arithmetic (including NaN/rounding), not mathematical reals. *)
      let retain e =
        match e with
        | Expr.UnOp (IsInt, inner) -> is_numeric inner
        | Expr.BinOp (a, (Equal | ValueEqual | FLessThan | FLessThanEqual), b)
          -> is_numeric a && is_numeric b
        | _ -> false
      in
      let subset = Expr.Set.filter retain fs in
      (* The precheck is a sufficient UNSAT proof only when the subset is a
         proper nonempty subformulation; a full or empty subset proves nothing
         about the mixed query. *)
      let proper_nonempty =
        (not (Expr.Set.is_empty subset))
        && Expr.Set.cardinal subset < Expr.Set.cardinal fs
      in
      if not proper_nonempty then false else proves_unsat ~caller_kind:"optional-numeric-subset" subset gamma

(* Sufficient UNSAT checks for observed mixed-theory obligations. Each selected
   core consists of original expressions. The final length check uses an
   explicitly weakened projection of an original core. We add no axioms and
   never infer SAT from a subset or projection. At most one core per shape is
   tried; native SAT/unknown preserves the complete fallback. *)
let original_unsat_precheck (fs : Expr.Set.t) (gamma : typenv) : bool =
  if (not !Config.Verification.total) || !Config.under_approximation then false
  else
    let expressions = Expr.Set.elements fs in
    let core atoms =
      let selected = Expr.Set.of_list atoms in
      if
        Expr.Set.cardinal selected = List.length atoms
        && Expr.Set.subset selected fs
        && Expr.Set.cardinal selected < Expr.Set.cardinal fs
      then Some selected
      else None
    in
    let try_shape select =
      match List.find_map select expressions with
      | None -> false
      | Some selected -> proves_unsat ~caller_kind:"optional-original-core" selected gamma
    in
    let number = function
      | Expr.LVar n -> Hashtbl.find_opt gamma n = Some Type.NumberType
      | _ -> false
    in
    (* The original pair stays unchanged. ValueEqual assumptions are separate
       exact-bit cases: native coverage must precede every native branch proof.
       They are never labelled or cached as an original-subset core. *)
    let literal_rank_split () =
      let one n = Int64.bits_of_float n = Int64.bits_of_float 1. in
      let rank_variable = function
        | Expr.BinOp
            ((BinOp ((UnOp (NumToInt,
                BinOp (BinOp ((LVar _ as variable), FMinus, Lit (Num down)),
                       FPlus, Lit (Num up))) as rank), ILessThan, Lit (Int zero))),
             Or, BinOp (UnOp (NumToInt,
                 BinOp (same_variable, FPlus, Lit (Num next))),
               ILessThanEqual, same_rank))
          when number variable && one down && one up && one next
               && Z.equal zero Z.zero && Expr.equal variable same_variable
               && Expr.equal rank same_rank -> Some variable
        | _ -> None
      in
      let candidates = List.concat_map (fun failed ->
        match rank_variable failed with
        | None -> []
        | Some variable -> List.filter_map (function
            | (Expr.BinOp ((LVar _ as left), Equal, Lit (Num value)) as binding)
            | (Expr.BinOp (Lit (Num value), Equal, (LVar _ as left)) as binding)
              when Expr.equal left variable && Float.is_finite value
                   && Option.is_some (core [binding; failed]) ->
                Some (binding, failed, variable, value)
            | _ -> None) expressions) expressions in
      match candidates with
      | [(binding, failed, variable, value)] ->
          let values = if value = 0. then
              [0.; Int64.float_of_bits Int64.min_int] else [value] in
          let identities = List.map (fun value ->
            Expr.BinOp (variable, ValueEqual, Expr.num value)) values in
          let covered = match identities with
            | [identity] -> identity
            | [positive; negative] -> Expr.BinOp (positive, Or, negative)
            | _ -> assert false in
          proves_unsat
            (Expr.Set.of_list [binding; Expr.UnOp (Not, covered)]) gamma
          && List.for_all (fun identity -> proves_unsat
               (Expr.Set.of_list [binding; failed; identity]) gamma) identities
      | _ -> false
    in
    (* Select only two unchanged original atoms: a Number literal binding and
       a comparison it contradicts. Host arithmetic chooses an optional core;
       only native binary64 UNSAT proves anything about the complete query. *)
    let literal_comparison = function
      | (Expr.BinOp ((LVar x as variable),
          ((FLessThan | FLessThanEqual) as op), Lit (Num bound)) as comparison)
        when number variable ->
          List.find_map (function
            | (Expr.BinOp (LVar y, (Equal | ValueEqual), Lit (Num value)) as binding)
            | (Expr.BinOp (Lit (Num value), (Equal | ValueEqual), LVar y) as binding)
              when x = y && not (if op = FLessThan then value < bound
                                 else value <= bound) -> core [ comparison; binding ]
            | _ -> None) expressions
      | (Expr.BinOp (Lit (Num bound),
          ((FLessThan | FLessThanEqual) as op), (LVar x as variable)) as comparison)
        when number variable ->
          List.find_map (function
            | (Expr.BinOp (LVar y, (Equal | ValueEqual), Lit (Num value)) as binding)
            | (Expr.BinOp (Lit (Num value), (Equal | ValueEqual), LVar y) as binding)
              when x = y && not (if op = FLessThan then bound < value
                                 else bound <= value) -> core [ comparison; binding ]
            | _ -> None) expressions
      | _ -> None
    in
    let finite_add = function
      | (Expr.UnOp (Not, BinOp (Lit (Num lower), FLessThanEqual,
           BinOp ((BinOp ((LVar _ as value), FMinus, Lit (Num 1.)) as predecessor),
             FMinus, Lit (Num 1.)))) as failed)
        when lower = -. Float.max_float && number value ->
          (* Shared by entailment and satisfiability. Both atoms are original;
             only native UNSAT may discharge the complete query. *)
          core [failed; Expr.UnOp (IsInt, predecessor)]
      | (Expr.UnOp (Not, BinOp (
           BinOp ((BinOp ((LVar _ as value), FMinus, Lit (Num 1.)) as predecessor),
             FMinus, Lit (Num 1.)), FLessThanEqual, Lit (Num upper))) as failed)
        when upper = Float.max_float && number value ->
          (* NumToInt definedness checks both finite bounds. *)
          core [failed; Expr.UnOp (IsInt, predecessor)]
      | (Expr.UnOp (Not, UnOp (IsInt,
           BinOp ((LVar _ as p), FPlus, Lit (Num 1.)))) as failed)
        when number p ->
          core [ failed; Expr.UnOp (IsInt, p) ]
      | (Expr.UnOp
           (Not, BinOp ((BinOp ((LVar _ as p), FPlus, Lit (Num 1.)) as sum),
                        Equal, same)) as failed)
        when Expr.equal sum same && number p ->
          core [ failed; Expr.UnOp (IsInt, p) ]
      | _ -> None
    in
    let code_upper = function
      | (Expr.UnOp
           (Not, BinOp ((BinOp (_, Utf16CodeUnit, _) as code),
                        FLessThanEqual, (Lit (Num _) as bound))) as failed) ->
          core [ failed; Expr.UnOp (Not, BinOp (bound, FLessThan, code)) ]
      | _ -> None
    in
    let length_index = function
      | (Expr.BinOp
           ((UnOp (Utf16Len, LVar s) as length), ILessThanEqual,
            UnOp (NumToInt, UnOp (ToIntOp,
              (BinOp ((LVar _ as p), FPlus, Lit (Num 1.)) as index)))) as failed)
        when Hashtbl.find_opt gamma s = Some Type.Utf16Type && number p ->
          let rounded = Expr.UnOp (IntToNum, length) in
          (* Find existing Number-length and nonnegative counter links. The
             exact safe-integer bounds remain original premises, not axioms. *)
          List.find_map
            (function
              | (Expr.BinOp ((LVar _ as n), Equal, rhs) as link)
                when Expr.equal rhs rounded && number n ->
                  List.find_map
                    (function
                      | (Expr.BinOp (Lit (Num 0.), FLessThanEqual,
                                     (LVar _ as count)) as nonnegative)
                        when number count ->
                          core
                            [ failed;
                              Expr.UnOp (Not, BinOp (rounded, FLessThanEqual,
                                                     UnOp (ToIntOp, index)));
                              Expr.UnOp (IsInt, p);
                              nonnegative;
                              Expr.BinOp (count, FLessThanEqual, p);
                              link;
                              Expr.BinOp (n, FLessThanEqual,
                                          Lit (Num 9007199254740991.));
                              Expr.BinOp (p, FLessThan, n);
                              Expr.BinOp (length, ILessThanEqual,
                                          Lit (Int (Z.of_string "9007199254740991")));
                              Expr.BinOp (index, FLessThan, n) ]
                      | _ -> None)
                    expressions
              | _ -> None)
            expressions
      | _ -> None
    in
    let mask_test code =
      Expr.BinOp
        (BinOp (UnOp (ToInt32Op, code), BitwiseAndF, Lit (Num 64512.)),
         Equal, Lit (Num 56320.))
    in
    let mask_lower = function
      | (Expr.UnOp
           (Not, BinOp (Lit (Num 56320.), FLessThanEqual,
                        (BinOp (_, Utf16CodeUnit, _) as code))) as failed) ->
          core [ failed; mask_test code ]
      | _ -> None
    in
    let mask_upper = function
      | (Expr.UnOp
           (Not, BinOp ((BinOp (_, Utf16CodeUnit, _) as code),
                        FLessThanEqual, Lit (Num 57343.))) as failed) ->
          core [ failed; mask_test code ]
      | _ -> None
    in
    let mask_complement = function
      | (Expr.UnOp
           (Not, BinOp (Lit (Num 57343.), FLessThan,
                        (BinOp (_, Utf16CodeUnit, _) as code))) as failed) ->
          core [ failed;
                 Expr.UnOp (Not, BinOp (code, FLessThan, Lit (Num 56320.)));
                 Expr.UnOp (Not, mask_test code) ]
      | _ -> None
    in
    let length_projection = function
      | (Expr.BinOp
           ((UnOp (IntToNum, UnOp (Utf16Len, LVar s)) as rounded),
            FLessThanEqual, (UnOp (ToIntOp,
              (BinOp ((LVar _ as p), FPlus, Lit (Num 1.)) as sum)) as index))
         as failed)
        when Hashtbl.find_opt gamma s = Some Type.Utf16Type && number p ->
          List.find_map
            (function
              | (Expr.BinOp ((LVar _ as n), Equal, rhs) as link)
                when Expr.equal rhs rounded && number n ->
                  let integral = Expr.UnOp (IsInt, p) in
                  let below = Expr.BinOp (sum, FLessThan, n) in
                  (match core [ failed; integral; link; below ] with
                  | None -> None
                  | Some _ ->
                      (* IntToNum produces a Number. Replacing this identical
                         subterm twice with one unconstrained fresh Number is
                         an overapproximation: every original model extends to
                         a projected model. Only native UNSAT can conclude.
                         Generic Number comparison also drops the specialised
                         UTF-16 index guard; that only weakens the formula. *)
                      let names = Expr.Set.fold
                        (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
                      let rec fresh i =
                        let name = "#utf16_length_projection_" ^ string_of_int i in
                        if Hashtbl.mem gamma name || SS.mem name names then
                          fresh (i + 1)
                        else name
                      in
                      let name = fresh 0 in
                      let abstract = Expr.LVar name in
                      let projected_gamma = Hashtbl.copy gamma in
                      Hashtbl.add projected_gamma name Type.NumberType;
                      Some
                        (Expr.Set.of_list
                           [ integral;
                             Expr.BinOp (n, Equal, abstract);
                             Expr.BinOp (abstract, FLessThanEqual, index);
                             below ], projected_gamma))
              | _ -> None)
            expressions
      | _ -> None
    in
    (* A list-prefix restoration check may retain a concrete list equal to
       prefix ++ suffix while asking whether take(list, length-list - suffix)
       ++ suffix differs. Submit only that original equality and failed goal;
       native UNSAT proves the larger conjunction. No list law is assumed. *)
    let list_prefix = function
      | (Expr.UnOp (Not, BinOp ((EList items as values),
          (Equal | ValueEqual), NOp (LstCat,
            [ LstSub (whole, Lit (Int zero), length); (LVar tail as suffix) ])))
          as failed)
        when Z.equal zero Z.zero
          && Hashtbl.find_opt gamma tail = Some Type.ListType ->
          let expected = Expr.BinOp
            (Expr.Lit (Int (Z.of_int (List.length items))), IPlus,
             BinOp (Lit (Int Z.minus_one), ITimes, UnOp (LstLen, suffix))) in
          if not (Expr.equal length expected) then None else
          List.find_map (function
            | (Expr.BinOp (left, (Equal | ValueEqual), right) as link)
              when (Expr.equal left values && Expr.equal right whole)
                || (Expr.equal right values && Expr.equal left whole) ->
                core [ failed; link ]
            | _ -> None) expressions
      | _ -> None
    in
    (* The inverse prefix check asks whether the concatenated prefix itself
       differs from take(prefix ++ suffix, known-length - suffix-length).
       Only the original decomposition and failed goal are submitted. *)
    let list_prefix_only = function
      | (Expr.UnOp (Not, BinOp ((NOp (LstCat, _) as prefix),
          (Equal | ValueEqual), LstSub ((NOp (LstCat, parts) as whole),
            Lit (Int zero), length))) as failed)
        when Z.equal zero Z.zero ->
          (match List.rev parts with
           | (LVar tail as suffix) :: before
             when Hashtbl.find_opt gamma tail = Some Type.ListType
               && Expr.equal prefix (Expr.NOp (LstCat, List.rev before)) ->
               List.find_map (function
                 | (Expr.BinOp ((EList items), (Equal | ValueEqual), right) as link)
                   when Expr.equal right whole ->
                     let expected = Expr.BinOp
                       (Expr.Lit (Int (Z.of_int (List.length items))), IPlus,
                        BinOp (Lit (Int Z.minus_one), ITimes,
                          UnOp (LstLen, suffix))) in
                     if Expr.equal length expected then core [ failed; link ]
                     else None
                 | _ -> None) expressions
           | _ -> None)
      | _ -> None
    in
    (* Keep275 q472/q478 retain a symbolic prefix followed by one head.
       Select only the failed original equality and its two original length
       links. No sequence law, witness, projection or fresh fact is added;
       only native UNSAT of this proper original-expression subset suffices. *)
    let symbolic_slice_info = function
      | (Expr.LstSub
           (NOp (LstCat, [ (LVar before as prefix); (EList [ LVar head ] as one); LVar tail ]),
            Lit (Int zero),
            (UnOp (NumToInt, BinOp ((LVar index as counter), FPlus, Lit (Num step))) as length)))
        when Z.equal zero Z.zero && step = 1.
          && Hashtbl.find_opt gamma before = Some Type.ListType
          && Hashtbl.find_opt gamma tail = Some Type.ListType
          && Hashtbl.find_opt gamma head = Some Type.Utf16Type
          && Hashtbl.find_opt gamma index = Some Type.NumberType ->
          Some (Expr.NOp (LstCat, [ prefix; one ]), prefix, counter, length)
      | _ -> None
    in
    let symbolic_slice_core failed slice =
      match symbolic_slice_info slice with
      | None -> None
      | Some (_, prefix, counter, length) ->
          let count = Expr.UnOp (NumToInt, counter) in
          let find_link a b = List.find_opt (function
            | Expr.BinOp (left, (Equal | ValueEqual), right) ->
                (Expr.equal left a && Expr.equal right b)
                || (Expr.equal right a && Expr.equal left b)
            | _ -> false) expressions in
          (match find_link count (Expr.UnOp (LstLen, prefix)),
             find_link length (Expr.BinOp (Expr.int 1, IPlus, count)) with
          | Some prefix_length, Some successor -> core [ failed; prefix_length; successor ]
          | _ -> None)
    in
    let symbolic_prefix_slice = function
      | (Expr.UnOp (Not, BinOp (left, (Equal | ValueEqual), right)) as failed) ->
          let select prefix slice = match symbolic_slice_info slice with
            | Some (expected, _, _, _) when Expr.equal prefix expected ->
                symbolic_slice_core failed slice
            | _ -> None in
          (match select left right with Some _ as selected -> selected
           | None -> select right left)
      | _ -> None
    in
    let symbolic_prefix_cons = function
      | (Expr.UnOp (Not, BinOp (left, (Equal | ValueEqual), right)) as failed) ->
          let select slice = function
            | Expr.NOp (LstCat,
                [ EList [ BinOp (LstSub (same, Lit (Int zero), Lit (Int one)),
                    LstNth, Lit (Int index)) ]; UnOp (Cdr, rest) ])
              when Z.equal zero Z.zero && Z.equal one Z.one && Z.equal index Z.zero
                && Expr.equal same slice && Expr.equal rest slice ->
                symbolic_slice_core failed slice
            | _ -> None in
          (match select left right with Some _ as selected -> selected
           | None -> select right left)
      | _ -> None
    in
    (* Keep276 q474/q476 ask for the suffix after the symbolic prefix/head.
       Keep the exact integer length AST and both original length links;
       only native UNSAT of this proper original subset can discharge it. *)
    let symbolic_suffix_slice = function
      | (Expr.UnOp (Not, BinOp (left, (Equal | ValueEqual), right)) as failed) ->
          let select suffix = function
            | Expr.LstSub
                (NOp (LstCat, [ (LVar before as prefix); EList [ LVar head ];
                   (LVar tail as rest) ]),
                 (UnOp (NumToInt, BinOp ((LVar index as counter), FPlus,
                    Lit (Num step))) as start), length)
              when step = 1. && Expr.equal suffix rest
                && Hashtbl.find_opt gamma before = Some Type.ListType
                && Hashtbl.find_opt gamma tail = Some Type.ListType
                && Hashtbl.find_opt gamma head = Some Type.Utf16Type
                && Hashtbl.find_opt gamma index = Some Type.NumberType ->
                let expected = Expr.BinOp (Expr.int 1, IPlus,
                  BinOp (BinOp (UnOp (LstLen, rest), IPlus, UnOp (LstLen, prefix)),
                    IPlus, BinOp (Expr.int (-1), ITimes, start))) in
                if not (Expr.equal length expected) then None else
                let count = Expr.UnOp (NumToInt, counter) in
                let find_link a b = List.find_opt (function
                  | Expr.BinOp (left, (Equal | ValueEqual), right) ->
                      (Expr.equal left a && Expr.equal right b)
                      || (Expr.equal right a && Expr.equal left b)
                  | _ -> false) expressions in
                (match find_link count (Expr.UnOp (LstLen, prefix)),
                   find_link start (Expr.BinOp (Expr.int 1, IPlus, count)) with
                 | Some prefix_length, Some successor ->
                     let integer = Expr.UnOp (IsInt, counter) in
                     let nonnegative = Expr.BinOp (Expr.num 0., FLessThanEqual, counter) in
                     let upper = Expr.BinOp (counter, FLessThanEqual, Expr.num 4294967294.) in
                     if List.for_all (fun premise -> Expr.Set.mem premise fs)
                       [ integer; nonnegative; upper ] then
                        Option.map (fun selected -> selected,
                          [before,Type.ListType;tail,Type.ListType;
                           head,Type.Utf16Type;index,Type.NumberType])
                          (core [ failed; prefix_length; successor;
                            integer; nonnegative; upper ])
                     else None
                 | _ -> None)
            | _ -> None in
          (match select left right with Some _ as selected -> selected
           | None -> select right left)
      | _ -> None
    in
    let try_symbolic caller_kind select =
      match List.find_map select expressions with
      | None -> false
      | Some selected -> proves_unsat ~caller_kind selected gamma
    in
    let try_suffix () =
      match List.find_map symbolic_suffix_slice expressions with
      | None -> false
      | Some (selected,roles) -> suffix_alpha_copy fs selected gamma roles
          || proves_unsat ~caller_kind:"optional-symbolic-suffix-slice" selected gamma
    in
    let try_projection () =
      match List.find_map length_projection expressions with
      | None -> false
      | Some (projected, projected_gamma) ->
          proves_unsat ~caller_kind:"optional-length-projection" projected projected_gamma
    in
    (* Select only unchanged original atoms. Even a licensed finite-literal
       shape is merely a candidate: native UNSAT remains authoritative. *)
    let subtraction_ceiling = function
      | (Expr.UnOp (Not,
           BinOp (BinOp (Lit (Num c), FMinus, (LVar name as variable)),
                  FLessThanEqual, Lit (Num ceiling))) as failed)
        when number variable && Float.is_finite c
             && Float.is_finite ceiling && c <= ceiling ->
          let nonnegative = List.find_opt (function
            | Expr.BinOp (Lit (Num zero), FLessThanEqual, LVar same) ->
                same = name && zero = 0.
            | _ -> false) expressions in
          (* Choose the weakest eligible retained upper, never a derived one.
             Equal literal values keep the first original atom in Set order. *)
          let upper = List.fold_left (fun chosen -> function
            | (Expr.BinOp (LVar same, FLessThanEqual, Lit (Num limit)) as atom)
              when same = name && Float.is_finite limit && limit >= 0. ->
                (match chosen with
                 | Some (previous, _) when previous >= limit -> chosen
                 | _ -> Some (limit, atom))
            | _ -> chosen) None expressions in
          (match nonnegative, upper with
           | Some lower, Some (_, upper) -> core [failed; lower; upper]
           | _ -> None)
      | (Expr.UnOp (Not,
           BinOp (Lit (Num floor), FLessThanEqual,
                  BinOp (Lit (Num c), FMinus, (LVar name as variable)))) as failed)
        when number variable && Float.is_finite floor
             && Float.is_finite c && floor <= 0. ->
          (* The retained upper excludes NaN/+Infinity. Negative infinity
             gives +Infinity; finite x <= c gives a nonnegative difference.
             This only selects an original pair for native UNSAT validation. *)
          let upper = List.fold_left (fun chosen -> function
            | (Expr.BinOp (LVar same, FLessThanEqual, Lit (Num limit)) as atom)
              when same = name && Float.is_finite limit && limit <= c ->
                (match chosen with
                 | Some (previous, _) when previous >= limit -> chosen
                 | _ -> Some (limit, atom))
            | _ -> chosen) None expressions in
          (match upper with
           | Some (_, upper) -> core [failed; upper]
           | None -> None)
      | (Expr.UnOp (Not,
           BinOp (Lit (Num floor), FLessThanEqual,
             BinOp (Lit (Num c), FMinus,
               BinOp ((LVar name as variable), FPlus, Lit (Num step))))) as failed)
        when number variable && Float.is_finite floor && Float.is_finite c
             && Float.is_finite step && floor <= 0. ->
          (* Keep the original alias and matching addition, never substitute.
             Multiple one-hop alias atoms are deliberately ineligible. *)
          let aliases = List.filter_map (function
            | (Expr.BinOp (LVar left, Equal, LVar right) as atom)
              when left = name && right <> name && number (Expr.LVar right) ->
                Some (right, atom)
            | (Expr.BinOp (LVar left, Equal, LVar right) as atom)
              when right = name && left <> name && number (Expr.LVar left) ->
                Some (left, atom)
            | _ -> None) expressions in
          (match aliases with
           | [(alias, link)] ->
               let upper = List.fold_left (fun chosen -> function
                 | (Expr.BinOp
                      (BinOp (LVar same, FPlus, Lit (Num amount)),
                       FLessThanEqual, Lit (Num limit)) as atom)
                   when same = alias && Float.is_finite limit && limit <= c
                        && Int64.bits_of_float amount = Int64.bits_of_float step ->
                     (match chosen with
                      | Some (previous, _) when previous >= limit -> chosen
                      | _ -> Some (limit, atom))
                 | _ -> chosen) None expressions in
               (match upper with
                | Some (_, upper) -> core [failed; link; upper]
                | None -> None)
           | _ -> None)
      | _ -> None
    in
    (* A candidate original pair, never an assumed binary64 order law. *)
    let strict_order_successor = function
      | (Expr.UnOp (Not,
           BinOp ((LVar _ as lower), FLessThan,
                  BinOp ((LVar _ as upper), FPlus, Lit (Num 1.)))) as failed)
        when number lower && number upper ->
          List.find_map (function
            | (Expr.BinOp (left, FLessThan, right) as ordered)
              when Expr.equal left lower && Expr.equal right upper ->
                core [failed; ordered]
            | _ -> None) expressions
      | _ -> None
    in
    literal_rank_split () || try_shape literal_comparison || try_shape finite_add
    || try_shape code_upper || try_shape length_index
    || try_shape mask_lower || try_shape mask_upper || try_shape mask_complement
    || try_shape list_prefix || try_shape list_prefix_only || try_projection ()
    || try_symbolic "optional-symbolic-prefix-slice" symbolic_prefix_slice
    || try_symbolic "optional-symbolic-prefix-cons" symbolic_prefix_cons
    || try_suffix () || try_shape subtraction_ceiling
    || try_shape strict_order_successor

(* Small bounded natural counters guide only an optional complete-query
   model search. Native SAT must validate every original assertion; a failed
   hint leaves all existing searches and the required-query policy unchanged. *)
let natural_counter_model fs gamma =
  (* Existing UTF16 witness paths keep their query order and bounds. *)
  let strings = object
    inherit [_] Visitors.iter as super
    val mutable observed = false
    method observed = observed
    method! visit_expr () e =
      (match e with
       | Expr.Lit (Utf16String _ | String _)
       | Expr.UnOp ((Utf16Len | Utf16ToNumber), _)
       | Expr.BinOp (_, (Utf16Nth | Utf16CodeUnit | Utf16Cat | Utf16Less), _) ->
           observed <- true
       | Expr.LVar x when Hashtbl.find_opt gamma x = Some Type.Utf16Type
           || Hashtbl.find_opt gamma x = Some Type.StringType -> observed <- true
       | _ -> ());
      super#visit_expr () e
  end in
  Expr.Set.iter (strings#visit_expr ()) fs;
  let counters = Expr.Set.fold (fun assertion names -> match assertion with
    | Expr.UnOp (IsInt, LVar x)
      when Hashtbl.find_opt gamma x = Some Type.NumberType ->
        let nonnegative = Expr.Set.mem
          (Expr.BinOp (Expr.num 0., FLessThanEqual, LVar x)) fs
          || Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThan, LVar x)) fs in
        let bounded = Expr.Set.exists (function
          | Expr.BinOp (LVar y, FLessThanEqual, Lit (Num limit))
            when x = y -> limit >= 0. && limit <= 9007199254740991.
          | _ -> false) fs in
        if nonnegative && bounded then SS.add x names else names
    | _ -> names) fs SS.empty in
  (* A single literal-bounded natural counter can also guide its original
     nonnegative integral predecessor. This selects a complete-query witness
     attempt only: no transitive bound or type is added to the symbolic state.
     Keep all existing multi-counter hints byte-for-byte on their old path. *)
  let ordered_lower =
    if SS.cardinal counters <> 1 then None else
    List.find_map (function
      | Expr.BinOp (LVar lower, FLessThan, LVar upper)
        when lower <> upper && SS.mem upper counters
          && Hashtbl.find_opt gamma lower = Some Type.NumberType
          && Expr.Set.mem (Expr.UnOp (IsInt, LVar lower)) fs
          && (Expr.Set.mem
                (Expr.BinOp (Expr.num 0., FLessThanEqual, LVar lower)) fs
              || Expr.Set.mem
                (Expr.BinOp (Expr.num 0., FLessThan, LVar lower)) fs) ->
          Some lower
      | _ -> None) (Expr.Set.elements fs) in
  let hinted_counters = match ordered_lower with
    | Some lower -> SS.add lower counters
    | None -> counters in
  if not !Config.Verification.total || strings#observed
     || SS.cardinal hinted_counters < 2 then None else
  let query = SS.fold (fun x acc ->
    let literal = Expr.Set.fold (fun assertion found -> match found, assertion with
      | None, Expr.BinOp (LVar y, (Equal | ValueEqual), Lit (Num value))
      | None, Expr.BinOp (Lit (Num value), (Equal | ValueEqual), LVar y)
        when x = y -> Some value
      | _ -> found) fs None in
    Expr.Set.add (Expr.BinOp (LVar x, ValueEqual,
      Expr.num (Option.value literal
        ~default:(if ordered_lower = Some x then 0. else 1.)))) acc)
    hinted_counters fs in
  if Expr.Set.equal query fs then None else
  try run_sat ~caller_kind:"optional-natural-counter" ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
      ~raw_unknown:true query gamma
  with SMT_unknown -> None

(* Previously-ineligible one-head trim feasibility may use a small existential
   witness. Preserve all old UTF16/rounded-length searches. Every hint is added
   only to the complete native query; no symbolic fact or type is produced. *)
let trimmed_counter_model fs gamma =
  let vars = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
  let of_type typ = SS.filter (fun x -> Hashtbl.find_opt gamma x = Some typ) vars in
  let heads = of_type Type.Utf16Type and numbers = of_type Type.NumberType in
  let rounded = object
    inherit [_] Visitors.iter as super
    val mutable observed = false
    method observed = observed
    method! visit_expr () e =
      (match e with Expr.UnOp (IntToNum, UnOp (Utf16Len, _)) -> observed <- true
       | _ -> ()); super#visit_expr () e
  end in
  Expr.Set.iter (rounded#visit_expr ()) fs;
  if not !Config.Verification.total || SS.cardinal heads <> 1
     || SS.cardinal numbers <> 3 || rounded#observed
     || not (SS.is_empty (of_type Type.StringType)) then None else
  let head = SS.choose heads in
  let empty = Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical "")) in
  let trimmed = Expr.UnOp (Utf16Trim, Expr.LVar head) in
  let trim_empty = Expr.Set.exists (function
    | Expr.BinOp (left, (Equal | ValueEqual), right) ->
        (left = trimmed && right = empty) || (left = empty && right = trimmed)
    | _ -> false) fs in
  let bounded_integer x = SS.mem x numbers
    && Expr.Set.mem (Expr.UnOp (IsInt, LVar x)) fs
    && Expr.Set.exists (function
      | Expr.BinOp (LVar y, FLessThanEqual, Lit (Num limit)) when x = y ->
          limit >= 0. && limit <= 9007199254740991.
      | _ -> false) fs in
  let natural x = bounded_integer x && Expr.Set.mem
    (Expr.BinOp (Expr.num 0., FLessThanEqual, LVar x)) fs in
  let shape = if not trim_empty then None else
    List.find_map (function
      | Expr.BinOp (LVar lower, FLessThan, LVar upper)
        when lower <> upper && natural lower && bounded_integer upper ->
          let remaining = SS.remove upper (SS.remove lower numbers) in
          let position = SS.choose remaining in
          if natural position && Expr.Set.mem
            (Expr.BinOp (LVar position, FLessThanEqual, LVar lower)) fs
          then Some (lower,upper,position) else None
      | _ -> None) (Expr.Set.elements fs) in
  match shape with None -> None | Some (lower,upper,position) ->
  let literal name default =
    Expr.Set.fold (fun assertion found -> match found, assertion with
      | None, Expr.BinOp (LVar x, (Equal | ValueEqual), (Lit _ as value))
      | None, Expr.BinOp ((Lit _ as value), (Equal | ValueEqual), LVar x)
        when x = name -> Some value
      | _ -> found) fs None |> Option.value ~default in
  let query = List.fold_left (fun acc (name,default) -> Expr.Set.add
    (Expr.BinOp (LVar name, ValueEqual, literal name default)) acc) fs
    [lower,Expr.num 0.; upper,Expr.num 1.; position,Expr.num 0.; head,empty] in
  try run_sat ~caller_kind:"optional-trimmed-counter" ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
      ~raw_unknown:true query gamma
  with SMT_unknown -> None

(* A nonblank trimmed head may use its own bounded complete-query witness.
   Default mode keeps its old search position. Strict-only mode recognizes a
   previously ineligible positive lower bound before generic counter search.
   Literal pins are respected; only validated full-query SAT returns a model. *)
let nonblank_counter_model ?(strict_only = false) fs gamma =
  let vars = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
  let of_type typ = SS.filter (fun x -> Hashtbl.find_opt gamma x = Some typ) vars in
  let heads = of_type Type.Utf16Type and numbers = of_type Type.NumberType in
  let rounded = object
    inherit [_] Visitors.iter as super
    val mutable observed = false
    method observed = observed
    method! visit_expr () e =
      (match e with Expr.UnOp (IntToNum, UnOp (Utf16Len, _)) -> observed <- true
       | _ -> ()); super#visit_expr () e
  end in
  Expr.Set.iter (rounded#visit_expr ()) fs;
  let empty = Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical "")) in
  let nonblank head =
    let trimmed = Expr.UnOp (Utf16Trim, Expr.LVar head) in
    Expr.Set.exists (function
      | Expr.UnOp (Not, Expr.BinOp (left, (Equal | ValueEqual), right)) ->
          (left = trimmed && right = empty) || (left = empty && right = trimmed)
      | _ -> false) fs in
  (* Strict mode binds the unique observed trim role, not every UTF16 variable
     in the owned frame. Other heads remain in the complete native query. *)
  let candidates = if strict_only then SS.filter nonblank heads else heads in
  if not !Config.Verification.total || (strict_only && !Config.under_approximation)
     || SS.cardinal candidates <> 1 || SS.cardinal numbers < 3 || rounded#observed
     || not (SS.is_empty (of_type Type.StringType)) then None else
  let head = SS.choose candidates in
  let trim_nonblank = nonblank head in
  let bounded_integer x = SS.mem x numbers
    && Expr.Set.mem (Expr.UnOp (IsInt, LVar x)) fs
    && Expr.Set.exists (function
      | Expr.BinOp (LVar y, FLessThanEqual, Lit (Num limit)) when x = y ->
          limit >= 0. && limit <= 9007199254740991.
      | _ -> false) fs in
  let natural x = bounded_integer x && Expr.Set.mem
    (Expr.BinOp (Expr.num 0., FLessThanEqual, LVar x)) fs in
  let lower_natural x = if not strict_only then natural x else
    bounded_integer x && not (natural x) && Expr.Set.mem
      (Expr.BinOp (Expr.num 0., FLessThan, LVar x)) fs in
  let shape = if not trim_nonblank then None else
    List.find_map (function
      | Expr.BinOp (LVar lower, FLessThan, LVar upper)
        when lower <> upper && lower_natural lower && bounded_integer upper ->
          let remaining = SS.remove upper (SS.remove lower numbers) in
          let positions = SS.filter (fun position -> natural position
            && Expr.Set.mem
              (Expr.BinOp (LVar position, FLessThanEqual, LVar lower)) fs)
            remaining in
          (* Extra Number variables license no role; ambiguous positions
             leave the original complete-query fallback untouched. *)
          (match SS.elements positions with
           | [position] -> Some (lower,upper,position)
           | _ -> None)
      | _ -> None) (Expr.Set.elements fs) in
  match shape with None -> None | Some (lower,upper,position) ->
  let literal name default =
    Expr.Set.fold (fun assertion found -> match found, assertion with
      | None, Expr.BinOp (LVar x, (Equal | ValueEqual), (Lit _ as value))
      | None, Expr.BinOp ((Lit _ as value), (Equal | ValueEqual), LVar x)
        when x = name -> Some value
      | _ -> found) fs None |> Option.value ~default in
  let distinct_counters =
    Expr.Set.mem (Expr.UnOp (Not, Expr.BinOp (LVar lower, ValueEqual, LVar position))) fs
    || Expr.Set.mem (Expr.UnOp (Not, Expr.BinOp (LVar position, ValueEqual, LVar lower))) fs in
  let lower_default,upper_default = if strict_only || distinct_counters then 1.,2. else 0.,1. in
  let make_query default_head = List.fold_left (fun acc (name,default) -> Expr.Set.add
    (Expr.BinOp (LVar name, ValueEqual, literal name default)) acc) fs
    [lower,Expr.num lower_default; upper,Expr.num upper_default; position,Expr.num 0.; head,Expr.Lit (Literal.Utf16String (Utils.Utf16.of_canonical default_head))] in
  let attempt caller_kind query =
    try run_sat ~caller_kind ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
      ~raw_unknown:true query gamma
    with SMT_unknown -> None in
  let original_query = make_query "a" in
  match attempt "optional-nonblank-counter" original_query with
  | Some _ as witness -> witness
  | None ->
      let whitespace_query = make_query " a" in
      if Expr.Set.equal original_query whitespace_query then None
      else attempt "optional-nonblank-whitespace-counter" whitespace_query


(* Neutral collection values guide only a complete-query SAT attempt. All
   retained formulas/types remain; failed hints cannot decide the original. *)
let neutral_collection_model fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None else
  let vars = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
  let of_type typ = SS.filter (fun x -> Hashtbl.find_opt gamma x = Some typ) vars in
  let numbers = of_type Type.NumberType and sets = of_type Type.SetType
  and lists = of_type Type.ListType in
  if SS.cardinal vars <> 4 || SS.cardinal numbers <> 2
     || SS.cardinal sets <> 1 || SS.cardinal lists <> 1 then None else
  let keys = SS.choose sets and values = SS.choose lists in
  let absent = Expr.Set.exists (function
    | Expr.UnOp (Not, BinOp (_, SetMem, LVar x)) -> x = keys
    | _ -> false) fs in
  let length_guard = Expr.Set.mem
    (Expr.BinOp (Expr.int 0, ILessThanEqual, UnOp (LstLen, LVar values))) fs in
  let shapes = List.filter_map (function
    | Expr.BinOp (LVar lower, FLessThanEqual, LVar upper)
      when lower <> upper && SS.mem lower numbers && SS.mem upper numbers ->
        let bounded = Expr.Set.exists (function
          | Expr.BinOp (LVar x, FLessThanEqual, Lit (Num limit)) when x = upper ->
              Float.is_finite limit && limit >= 0. && limit <= 9007199254740991.
          | _ -> false) fs in
        let retained = List.for_all (fun e -> Expr.Set.mem e fs)
          [Expr.UnOp (IsInt, LVar lower); Expr.UnOp (IsInt, LVar upper);
           Expr.BinOp (Expr.num 0., FLessThanEqual, LVar lower);
           Expr.BinOp (Expr.int 0, ILessThanEqual,
             UnOp (NumToInt, BinOp (LVar upper, FMinus, LVar lower)))] in
        if bounded && retained then Some (lower,upper) else None
    | _ -> None) (Expr.Set.elements fs) in
  match absent && length_guard, shapes with
  | true, [(lower,upper)] ->
      let excludes_zero = Expr.Set.exists (function
        | Expr.UnOp (Not, BinOp (LVar x, Equal, Lit (Num value)))
        | Expr.UnOp (Not, BinOp (Lit (Num value), Equal, LVar x))
          when x = upper -> value = 0.
        | _ -> false) fs in
      let upper_value = if excludes_zero then 1. else 0. in
      let query = List.fold_left (fun acc (name,value) -> Expr.Set.add
        (Expr.BinOp (LVar name, ValueEqual, value)) acc) fs
        [lower,Expr.num 0.; upper,Expr.num upper_value;
         keys,Expr.ESet []; values,Expr.EList []] in
      if Expr.Set.equal query fs then None else
      (try run_sat ~caller_kind:"optional-neutral-collection"
        ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
        ~raw_unknown:true query gamma with SMT_unknown -> None)
  | _ -> None

(* A strict natural gap with an original one-hop successor alias may try
   one complete-query witness. All existing facts/types remain; only native
   SAT can return a model. A failed hint leaves the required query unchanged. *)
let natural_gap_model fs gamma =
  let number x = Hashtbl.find_opt gamma x = Some Type.NumberType in
  let natural x = number x
    && Expr.Set.mem (Expr.UnOp (IsInt, LVar x)) fs
    && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual, LVar x)) fs
    && Expr.Set.exists (function
      | Expr.BinOp (LVar y, FLessThanEqual, Lit (Num bound)) when x = y ->
          bound >= 0. && bound <= 9007199254740991.
      | _ -> false) fs in
  let linked x y = Expr.Set.mem (Expr.BinOp (LVar x, Equal, LVar y)) fs
    || Expr.Set.mem (Expr.BinOp (LVar y, Equal, LVar x)) fs in
  let select upper successor = match upper, successor with
    | Expr.LVar upper, Expr.BinOp (LVar alias, FPlus, Lit (Num step))
      when step = 1. && number alias && natural upper ->
        Expr.Set.fold (fun e roles -> match e with
          | Expr.BinOp (LVar lower, FLessThan, LVar limit)
            when limit = upper && lower <> upper && alias <> lower
              && alias <> upper && natural lower && linked alias lower ->
                (lower, upper, alias) :: roles
          | _ -> roles) fs []
    | _ -> [] in
  if not !Config.Verification.total || !Config.under_approximation then None else
  let roles = Expr.Set.fold (fun e roles -> match e with
    | Expr.UnOp (Not, BinOp (left, ValueEqual, right)) ->
        select left right @ select right left @ roles
    | _ -> roles) fs [] |> List.sort_uniq Stdlib.compare in
  match roles with
  | [(lower, upper, _)] ->
      let query = List.fold_left (fun query (name, value) -> Expr.Set.add
        (Expr.BinOp (LVar name, ValueEqual, Expr.num value)) query)
        fs [lower, 0.; upper, 2.] in
      if Expr.Set.equal query fs then None else
      (try run_sat ~caller_kind:"optional-natural-counter"
        ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
        ~raw_unknown:true query gamma with SMT_unknown -> None)
  | _ -> None

(* One optional complete-current-query witness for the retained trace PRE.
   This recognises original ASTs and existing types only. The positive1 pin is
   a search candidate, never a symbolic-state fact or a domain restriction.
   Every assertion and Gamma entry survives. Only native validated SAT may
   decide; a failed candidate leaves the original required path unchanged. *)
let positive_trace_index_witness_query fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None
  else
    let eq a b = Expr.BinOp (a, Equal, b) in
    let le a b = Expr.BinOp (a, FLessThanEqual, b) in
    let ile a b = Expr.BinOp (a, ILessThanEqual, b) in
    let has_equal a b = Expr.Set.mem (eq a b) fs || Expr.Set.mem (eq b a) fs in
    let alias typ value = Expr.Set.fold (fun atom names -> match atom with
      | Expr.BinOp (LVar a, ValueEqual, LVar b) ->
          let matches name target = Expr.equal value (Expr.LVar target)
            && Hashtbl.find_opt gamma target = Some typ
            && Hashtbl.find_opt gamma name = None in
          if matches a b then a :: names else if matches b a then b :: names else names
      | _ -> names) fs [] |> List.sort_uniq String.compare in
    let candidates = Expr.Set.fold (fun atom found -> match atom with
      | Expr.UnOp (IsInt, (LVar name as index))
        when Hashtbl.find_opt gamma name = Some Type.NumberType ->
          let successor = Expr.BinOp (index, FPlus, Expr.num 1.) in
          let predecessor = Expr.BinOp (successor, FMinus, Expr.num 1.) in
          let count = Expr.UnOp (NumToInt,index) in
          let values = Expr.Set.fold (fun atom values -> match atom with
            | Expr.BinOp (BinOp (Lit (Int one), IPlus, cast), ILessThanEqual,
                UnOp (LstLen,(LVar list_name as list)))
              when Z.equal one Z.one && Expr.equal cast count
                && Hashtbl.find_opt gamma list_name = Some Type.ListType ->
                  list :: values
            | _ -> values) fs [] |> List.sort_uniq Stdlib.compare in
          List.fold_left (fun found values ->
            let length = Expr.UnOp (LstLen,values) in
            let retained = List.for_all (fun e -> Expr.Set.mem e fs)
              [Expr.UnOp (IsInt,successor); le (Expr.num 0.) index;
               le index (Expr.num 4294967295.);
               le successor (Expr.num 4294967295.);
               Expr.BinOp (Expr.num 0.,FLessThan,successor);
               ile (Expr.int 0) count; ile (Expr.int 0) length;
               ile length (Expr.int 4294967295)]
              && has_equal predecessor index
              && has_equal (Expr.UnOp (NumToInt,predecessor)) count
              && has_equal (Expr.UnOp (NumberToUtf16,predecessor))
                   (Expr.UnOp (NumberToUtf16,index)) in
            let currents = Expr.Set.fold (fun atom currents -> match atom with
              | Expr.BinOp (LVar a, ValueEqual, LVar b) ->
                  if Hashtbl.find_opt gamma a = None
                     && Hashtbl.find_opt gamma b = Some Type.Utf16Type
                  then Expr.LVar b :: currents
                  else if Hashtbl.find_opt gamma b = None
                     && Hashtbl.find_opt gamma a = Some Type.Utf16Type
                  then Expr.LVar a :: currents else currents
              | _ -> currents) fs [] |> List.sort_uniq Stdlib.compare in
            if not retained then found else
            List.fold_left (fun found current ->
              match alias Type.NumberType index, alias Type.ListType values,
                    alias Type.Utf16Type current with
              | [i],[v],[c] when List.length (List.sort_uniq String.compare
                    [i;v;c;name;
                     (match values with LVar n -> n | _ -> assert false);
                     (match current with LVar n -> n | _ -> assert false)]) = 6 ->
                  index :: found
              | _ -> found) found currents) found values
      | _ -> found) fs [] in
    (* Multiple complete role matches are ambiguous even if they share index. *)
    match candidates with
    | [index] ->
        let hint = Expr.BinOp (index,ValueEqual,Expr.num 1.) in
        if Expr.Set.mem hint fs then None else Some (Expr.Set.add hint fs)
    | [] ->
        (* Two smaller retained current frames lack the old joint support.
           Match existing typed roles/support only; preserve every extra
           constraint and Gamma row in the complete candidate. *)
        let roles typ = Hashtbl.fold (fun name actual names ->
          if actual = typ then name :: names else names) gamma [] in
        let supported_types = Hashtbl.fold (fun _ typ ok -> ok &&
          List.mem typ [Type.NumberType; Type.Utf16Type; Type.ListType;
                         Type.ObjectType]) gamma true in
        let names = Hashtbl.fold (fun name _ names -> name :: names) gamma [] in
        (match roles Type.NumberType, roles Type.Utf16Type, roles Type.ListType with
        | [index_name], [current_name], [values_name]
          when supported_types && List.length (List.sort_uniq String.compare names)
               = Hashtbl.length gamma
            && List.length (List.sort_uniq String.compare
                 [index_name; current_name; values_name]) = 3 ->
            let index = Expr.LVar index_name and current = Expr.LVar current_name
            and values = Expr.LVar values_name in
            let successor = Expr.BinOp (index, FPlus, Expr.num 1.) in
            let predecessor = Expr.BinOp (successor, FMinus, Expr.num 1.) in
            let count = Expr.UnOp (NumToInt, index) in
            let length = Expr.UnOp (LstLen, values) in
            let cast_lower = ile (Expr.int 0) count in
            let next_length = ile (Expr.BinOp (Expr.int 1, IPlus, count)) length in
            let nth_count = Expr.BinOp (values, LstNth, count) in
            let nth_predecessor = Expr.BinOp (values, LstNth,
                Expr.UnOp (NumToInt, predecessor)) in
            let common = List.for_all (fun e -> Expr.Set.mem e fs)
                [Expr.UnOp (IsInt, index); Expr.UnOp (IsInt, successor);
                 ile (Expr.int 0) length;
                 Expr.BinOp (Expr.num 0., FLessThan, successor);
                 le (Expr.num 0.) index; le index (Expr.num 4294967295.);
                 ile length (Expr.int 4294967295);
                 le successor (Expr.num 4294967295.)]
              && has_equal predecessor index
              && has_equal (Expr.UnOp (NumToInt, predecessor)) count
              && has_equal (Expr.UnOp (NumberToUtf16, predecessor))
                   (Expr.UnOp (NumberToUtf16, index)) in
            let aliases = alias Type.NumberType index, alias Type.ListType values,
                alias Type.Utf16Type current in
            let alias_frame = match aliases with
              | [i], [v], [c] ->
                  List.length (List.sort_uniq String.compare
                    [i; v; c; index_name; current_name; values_name]) = 6
                  && not (Expr.Set.mem cast_lower fs)
                  && not (has_equal current nth_count)
                  && not (has_equal current nth_predecessor)
              | _ -> false in
            let nth_frame = aliases = ([], [], [])
              && Expr.Set.mem cast_lower fs && Expr.Set.mem next_length fs
              && has_equal current nth_count && has_equal current nth_predecessor in
            let hint = Expr.BinOp (index, ValueEqual, Expr.num 1.) in
            if common && (alias_frame || nth_frame) && not (Expr.Set.mem hint fs)
            then Some (Expr.Set.add hint fs) else None
        | _ -> None)
    | _ -> None

let positive_trace_index_model fs gamma =
  match positive_trace_index_witness_query fs gamma with
  | None -> None
  | Some query ->
      let expressions fs = `List (List.map
        (fun e -> `String (Fmt.str "%a" Expr.pp e)) (Expr.Set.elements fs)) in
      with_native_smt_context
        (fun () -> `Assoc [
          ("operation",`String "positive-trace-index-complete-witness");
          ("original_fs",expressions fs);
          ("original_gamma",`String (Fmt.str "%a" pp_typenv gamma));
          ("hinted_fs",expressions query);
          ("added_candidate",expressions (Expr.Set.diff query fs)) ])
        (fun () -> try run_sat ~caller_kind:"optional-positive-trace-index"
          ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
          ~raw_unknown:true query gamma with SMT_unknown -> None)

(* A bounded index with an excluded formatted key can try one small witness.
   This pins only the complete-query search, never the symbolic state. A
   rejected or inconclusive hint preserves the required native fallback. *)
let formatted_index_model fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None else
  let vars = Expr.Set.fold (fun e acc -> SS.union (Expr.lvars e) acc) fs SS.empty in
  let typed typ = SS.filter (fun x -> Hashtbl.find_opt gamma x = Some typ) vars in
  let numbers = typed Type.NumberType and sets = typed Type.SetType in
  if SS.cardinal vars <> 2 || SS.cardinal numbers <> 1 || SS.cardinal sets <> 1
  then None else
  let name = SS.choose numbers and keys = SS.choose sets in
  let index = Expr.LVar name in
  let bounded = Expr.Set.exists (function
    | Expr.BinOp (LVar x, (FLessThan | FLessThanEqual), Lit (Num bound)) ->
        x = name && Float.is_finite bound && 0. <= bound && bound <= 4294967295.
    | _ -> false) fs in
  let fixed = Expr.Set.exists (function
    | Expr.BinOp (LVar x, ValueEqual, Lit (Num _))
    | Expr.BinOp (Lit (Num _), ValueEqual, LVar x) -> x = name
    | _ -> false) fs in
  if fixed || not bounded || not (List.for_all (fun e -> Expr.Set.mem e fs)
    [Expr.UnOp (IsInt,index);
     Expr.BinOp (Expr.num 0.,FLessThanEqual,index);
     Expr.UnOp (Not,BinOp (UnOp (NumberToUtf16,index),SetMem,LVar keys))])
  then None else
  let positive = Expr.Set.mem (Expr.BinOp (Expr.num 0.,FLessThan,index)) fs in
  let query = Expr.Set.add
    (Expr.BinOp (index,ValueEqual,Expr.num (if positive then 1. else 0.))) fs in
  try run_sat ~caller_kind:"optional-formatted-index"
    ~timeout_ms:(optional_timeout 1000) ~phase_selection:3
    ~raw_unknown:true query gamma with SMT_unknown -> None

let check_sat (fs : Expr.Set.t) (gamma : typenv) : model option =
  let key = formula_key fs gamma in
  match Formula_cache.find_opt sat_cache key with
  | Some result ->
      let () =
        L.verbose (fun m ->
            m "SAT check cached with result: %b" (Option.is_some result))
      in
      result
  | None ->
      let () = L.verbose (fun m -> m "SAT check not found in cache") in
      let ret =
        (* Both strict-positive and weak-zero nonblank states need a concrete
           head as well as counters. Try each existing complete head witness
           before the less constrained counter-only guess. All eligibility,
           budgets and full-query validation stay unchanged; failed guesses
           still reach every remaining attempt and required fallback. *)
        match nonblank_counter_model ~strict_only:true fs gamma with
        | Some _ as witness -> witness
        | None ->
        match nonblank_counter_model fs gamma with
        | Some _ as witness -> witness
        | None ->
        match nonempty_counter_model fs gamma with
        | Some _ as witness -> witness
        | None ->
        if original_unsat_precheck fs gamma then None
        else if numeric_unsat_precheck fs gamma then None
        else
          match natural_counter_model fs gamma with
          | Some _ as witness -> witness
          | None -> (match trimmed_counter_model fs gamma with
            | Some _ as witness -> witness
            | None -> (match seeded_model fs gamma with
              | Some _ as witness -> witness
              | None -> (match neutral_collection_model fs gamma with
                  | Some _ as witness -> witness
                  | None -> (match positive_trace_index_model fs gamma with
                    | Some _ as witness -> witness
                    | None ->
                      let complete_fs = with_checked_index_identities fs gamma in
                      (match natural_gap_model complete_fs gamma with
                       | Some _ as witness -> witness
                       | None -> (match formatted_index_model complete_fs gamma with
                         | Some _ as witness -> witness
                         | None -> exec_sat complete_fs gamma))))))
      in
      let () =
        L.verbose (fun m ->
            let f = Expr.conjunct (Expr.Set.elements fs) in
            m "Adding to cache : @[%a@]" Expr.pp f)
      in
      let () = Formula_cache.replace sat_cache key ret in
      ret

let is_sat (fs : Expr.Set.t) (gamma : typenv) : bool =
  Option.is_some (check_sat fs gamma)

let lift_model
    (model : model)
    (gamma : typenv)
    (subst_update : string -> Expr.t -> unit)
    (target_vars : Expr.Set.t) : unit =
  let cost = smt_cost_profile "model-lift" in
  let () = cost "lift" "none" in
  let () = reset_solver () in
  let () = List.iter cmd model.sort_declarations in
  let model_eval = (model_eval' !solver model.values).eval [] in

  let get_val x =
    try
      let x = x |> sanitize_identifier |> atom in
      model_eval x |> Option.some
    with UnexpectedSolverResponse _ -> None
  in

  let recover_number (n : sexp) : float option =
    let bits (value : sexp) =
      match value with
      | Atom s when String.starts_with ~prefix:"#b" s ->
          Z.of_string ("0b" ^ String.sub s 2 (String.length s - 2))
      | Atom s when String.starts_with ~prefix:"#x" s ->
          Z.of_string ("0x" ^ String.sub s 2 (String.length s - 2))
      | _ -> raise Exit
    in
    try
      match n with
      | List [ Atom "fp"; fp_sign; exponent; significand ] ->
          let raw =
            Z.(
              logor
                (shift_left (bits fp_sign) 63)
                (logor (shift_left (bits exponent) 52) (bits significand)))
          in
          let raw =
            if Z.testbit raw 63 then Z.sub raw (Z.shift_left Z.one 64) else raw
          in
          Some (Int64.float_of_bits (Z.to_int64 raw))
      | List [ Atom "_"; Atom value; Atom "11"; Atom "53" ] -> (
          match value with
          | "+zero" -> Some 0.
          | "-zero" -> Some (-0.)
          | "+oo" -> Some infinity
          | "-oo" -> Some neg_infinity
          | "NaN" -> Some nan
          | _ -> None)
      | _ -> None
    with Exit | Invalid_argument _ | Z.Overflow -> None
  in

  let recover_int (n : sexp) : Z.t option =
    try Some (to_z n) with UnexpectedSolverResponse _ -> None
  in

  let recover_string (value : sexp) =
    let buffer = Buffer.create 32 in
    let rec append (part : sexp) =
      match part with
      | List [ Atom "as"; Atom "seq.empty"; _ ] -> ()
      | List (Atom "seq.++" :: values) -> List.iter append values
      | List [ Atom "seq.unit"; byte ] ->
          let code =
            match byte with
            | Atom s when String.starts_with ~prefix:"#x" s ->
                int_of_string ("0x" ^ String.sub s 2 (String.length s - 2))
            | Atom s when String.starts_with ~prefix:"#b" s ->
                int_of_string ("0b" ^ String.sub s 2 (String.length s - 2))
            | List [ Atom "_"; Atom s; Atom "8" ]
              when String.starts_with ~prefix:"bv" s ->
                int_of_string (String.sub s 2 (String.length s - 2))
            | _ -> raise Exit
          in
          if code < 0 || code > 255 then raise Exit;
          Buffer.add_char buffer (Char.chr code)
      | _ -> raise Exit
    in
    try
      append value;
      Some (Buffer.contents buffer)
    with Exit | Failure _ | Invalid_argument _ -> None
  in

  let lift_val (x : string) : Literal.t option =
    let* gil_type = Hashtbl.find_opt gamma x in
    let* v = get_val x in
    match gil_type with
    | NumberType ->
        let+ n = recover_number v in
        Literal.Num n
    | IntType ->
        let+ n = recover_int v in
        Literal.Int n
    | StringType ->
        let+ bytes = recover_string v in
        Literal.String bytes
    | Utf16Type ->
        let+ bytes = Utf16.recover v in
        Literal.Utf16String (Utils.Utf16.of_canonical bytes)
    | BooleanType -> (
        match v with
        | Atom "true" -> Some (Literal.Bool true)
        | Atom "false" -> Some (Literal.Bool false)
        | _ -> None)
    | _ -> None
  in

  let () = L.verbose (fun m -> m "Inside lift_model") in
  target_vars
  |> Expr.Set.iter (fun x ->
         let x =
           match x with
           | LVar x -> x
           | _ ->
               exceptf "INTERNAL ERROR: SMT lifting of a non-logical variable"
         in
         let v = lift_val x in
         let () =
           L.verbose (fun m ->
               let binding =
                 v
                 |> Option.fold
                      ~some:(Fmt.to_to_string Literal.pp)
                      ~none:"NO BINDING!"
               in
               m "SMT binding for %s: %s\n" x binding)
         in
         v |> Option.iter (fun v -> subst_update x (Expr.Lit v)));
  cost "done" "none"

(* Standalone preparation controls link the real verifier but must never start
   SMT. Close the untouched solver before module initialization can spawn it;
   existing terminal guards reject any later initialization or solver access.
   Ordinary verifier startup retains the original eager initialization. *)
let () =
  if Sys.getenv_opt "GILLIAN_PREPARATION_CONTROLS_NO_SOLVER" = Some "1" then
    shutdown_solver ()
  else init_solver ()
