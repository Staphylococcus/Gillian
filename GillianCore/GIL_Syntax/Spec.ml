module SS = Containers.SS

(** Verification-only data; never a semantic caller postcondition. *)
type verifier_scope_binding = TypeDef__.verifier_scope_binding = {
  vsb_source : Expr.t;
  vsb_target : Expr.t;
}

let verifier_scope_binding_to_yojson = TypeDef__.verifier_scope_binding_to_yojson

let map_verifier_scope f b =
  { vsb_source = f b.vsb_source; vsb_target = f b.vsb_target }

(** {b Single GIL specifications}. *)
type st = TypeDef__.single_spec = {
  ss_pre : Asrt.t Location.located;  (** Precondition *)
  ss_posts : Asrt.t Location.located list;  (** Postcondition *)
  ss_variant : Expr.t option;  (** Variant *)
  ss_verifier_scope : verifier_scope_binding option;
  ss_flag : Flag.t;  (** Return flag *)
  ss_to_verify : bool;  (** Should the spec be verified? *)
  ss_label : (string * string list) option;
}

(** {b Full GIL specifications}. *)
type t = TypeDef__.spec = {
  spec_name : string;  (** Procedure/spec name *)
  spec_params : string list;  (** Executable procedure parameters *)
  spec_raw_args : string list option;  (** Complete checked call vector *)
  spec_sspecs : st list;  (** List of single specifications *)
  spec_normalised : bool;  (** If the spec is already normalised *)
  spec_incomplete : bool;  (** If the spec is incomplete *)
  spec_to_verify : bool;  (** Should the spec be verified? *)
  spec_location : Location.t option;
}

(** Creates a GIL specification given its components *)
let s_init
    ?(ss_verifier_scope : verifier_scope_binding option)
    ?(ss_label : (string * string list) option)
    (ss_pre : Asrt.t Location.located)
    (ss_posts : Asrt.t Location.located list)
    (ss_variant : Expr.t option)
    (ss_flag : Flag.t)
    (ss_to_verify : bool) : st =
  { ss_pre; ss_posts; ss_variant; ss_verifier_scope; ss_flag; ss_to_verify; ss_label }

let init
    ?spec_raw_args
    (spec_name : string)
    (spec_params : string list)
    (spec_sspecs : st list)
    (spec_normalised : bool)
    (spec_incomplete : bool)
    (spec_to_verify : bool)
    (spec_location : Location.t option) : t =
  {
    spec_name;
    spec_params;
    spec_raw_args;
    spec_sspecs;
    spec_normalised;
    spec_incomplete;
    spec_to_verify;
    spec_location;
  }

let extend (spec : t) (sspecs : st list) : t =
  { spec with spec_sspecs = sspecs @ spec.spec_sspecs }

let get_params (spec : t) : string list = spec.spec_params

(* A fixed complete argument vector, with the executable formals as its exact
   prefix. Surplus names are proof inputs, never executable parameters. *)
let input_params (spec : t) =
  Option.value ~default:spec.spec_params spec.spec_raw_args

let validate_raw_args (spec : t) =
  match spec.spec_raw_args with
  | None -> ()
  | Some names ->
      let invalid why = invalid_arg ("Invalid raw argument interface: " ^ why) in
      if not spec.spec_to_verify || spec.spec_incomplete || spec.spec_sspecs = []
         || List.exists (fun (s : st) -> not s.ss_to_verify) spec.spec_sspecs
      then invalid "requires a complete checked specification";
      let prefix = List.filteri (fun i _ -> i < List.length spec.spec_params) names in
      if prefix <> spec.spec_params then invalid "formal prefix differs";
      (* Quoted metadata slots permit keywords, but no lexer-incompatible
         escapes. This proof-only interface uses simple ASCII identifiers. *)
      let identifier name =
        Str.string_match (Str.regexp "[A-Za-z_][A-Za-z0-9_]*") name 0
        && Str.match_end () = String.length name in
      if List.exists (fun name -> not (identifier name) || not (Names.is_pvar_name name)) names
         || SS.cardinal (SS.of_list names) <> List.length names
      then invalid "empty or duplicate input name";
      List.iteri (fun i name ->
        if i >= List.length spec.spec_params && name = Names.return_variable
        then invalid "reserved surplus name") names

let summary_arity (spec : t) = List.length (input_params spec)

let pp_raw_args fmt spec =
  Option.iter (fun names -> Fmt.pf fmt " raw_args(%a)"
    Fmt.(list ~sep:comma Dump.string) names) spec.spec_raw_args

let pp_verifier_scope fmt b =
  Fmt.pf fmt " verify_scope(%a; %a)" Expr.pp b.vsb_source Expr.pp b.vsb_target

(* Reduction may decompose the scope list; its fresh final witness must survive
   in each public alternative. This check supplies no value for that witness. *)
let validate_verifier_scope ?(exact_target = false) (s : st) =
  match s.ss_verifier_scope with
  | None -> ()
  | Some b ->
      let invalid why = invalid_arg ("Invalid verifier scope binding: " ^ why) in
      if s.ss_flag <> Flag.Normal || not s.ss_to_verify then
        invalid "requires a verified normal case";
      (match b.vsb_source with
      | Expr.PVar name when name <> "" -> ()
      | _ -> invalid "source must be a program variable");
      let witness =
        match b.vsb_target with
        | Expr.EList xs -> (match List.rev xs with
            | Expr.LVar v :: _ -> v
            | _ -> invalid "target must end in a fresh logical witness")
        | _ -> invalid "target must be a scope list"
      in
      if SS.mem witness (Asrt.lvars (fst s.ss_pre)) then
        invalid "target witness occurs in PRE";
      if s.ss_posts = [] ||
         List.exists (fun (p, _) -> not (SS.mem witness (Asrt.lvars p))) s.ss_posts
      then invalid "orphan target witness";
      if exact_target then
        List.iter (fun (post, _) ->
          let found = ref false in
          let visitor = object
            inherit [_] Visitors.iter as super
            method! visit_expr () e =
              if Expr.equal e b.vsb_target then found := true;
              super#visit_expr () e
          end in
          visitor#visit_assertion () post;
          if not !found then invalid "target is not the public scope expression")
          s.ss_posts

let verifier_posts (s : st) =
  validate_verifier_scope s;
  match s.ss_verifier_scope with
  | None -> s.ss_posts
  | Some b ->
      List.map (fun (post, loc) ->
        (Asrt.Pure (Expr.BinOp (b.vsb_source, Equal, b.vsb_target)) :: post, loc))
        s.ss_posts

let verifier_scope_source = function
  | None -> None
  | Some { vsb_source = Expr.PVar name; _ } -> Some name
  | Some _ -> invalid_arg "Invalid verifier scope source"

let require_verifier_scope_source binding ~mem =
  match verifier_scope_source binding with
  | Some name when not (mem name) ->
      Error ("Missing final-store verifier scope source: " ^ name)
  | _ -> Ok ()

(* Explicit actual final values witness existing public POST existentials.
   This adds obligations to verification, never assumptions or caller posts. *)
let validate_final_locals (s : st) bindings =
  if bindings <> [] then (
    let invalid why = invalid_arg ("Invalid final-local binding: " ^ why) in
    if s.ss_flag <> Flag.Normal || not s.ss_to_verify then
      invalid "requires a verified normal case";
    let sources = ref SS.empty and targets = ref SS.empty in
    List.iter (fun b ->
      let source = match b.vsb_source with
        | Expr.PVar name when name <> "" -> name
        | _ -> invalid "source must be a program variable" in
      let target = match b.vsb_target with
        | Expr.LVar name when name <> "" -> name
        | _ -> invalid "target must be a logical variable" in
      if SS.mem source !sources || SS.mem target !targets then
        invalid "duplicate source or target";
      sources := SS.add source !sources; targets := SS.add target !targets;
      if SS.mem target (Asrt.lvars (fst s.ss_pre)) then
        invalid "target occurs in PRE";
      if s.ss_posts = [] || List.exists (fun (p,_) ->
          not (SS.mem target (Asrt.lvars p))) s.ss_posts then
        invalid "target absent from a public POST";
      Option.iter (fun scope ->
        if SS.mem target (Expr.lvars scope.vsb_target) then
          invalid "target overlaps verifier scope") s.ss_verifier_scope) bindings)

let final_local_posts bindings posts =
  List.map (fun (post,loc) ->
    List.map (fun b -> Asrt.Pure (Expr.BinOp
      (b.vsb_source, ValueEqual, b.vsb_target))) bindings @ post, loc) posts

let require_final_local_sources bindings ~mem =
  List.fold_left (fun result b -> match result, b.vsb_source with
    | Error _, _ -> result
    | Ok (), Expr.PVar name when mem name -> Ok ()
    | Ok (), Expr.PVar name -> Error ("Missing final-store proof local: " ^ name)
    | Ok (), _ -> invalid_arg "Invalid final-local source") (Ok ()) bindings

let pp_sspec fmt sspec =
  let pp_lab fmt' (lab, exs) =
    match exs with
    | [] -> Fmt.pf fmt' "<%s>@\n" lab
    | exs -> Fmt.pf fmt' "<%s: %a>@\n" lab Fmt.(list ~sep:comma string) exs
  in
  Fmt.pf fmt "%a[[  @[<hv 0>%a@]  ]]@\n[[  @[<hv 0>%a@]  ]]%a@\n%s"
    (Fmt.option pp_lab) sspec.ss_label Asrt.pp (fst sspec.ss_pre)
    (Fmt.list ~sep:(Fmt.any ";@\n") Asrt.pp)
    (List.map fst sspec.ss_posts)
    (Fmt.option pp_verifier_scope) sspec.ss_verifier_scope
    (Flag.str sspec.ss_flag)

let pp fmt spec =
  let pp_incomplete fmt = function
    | true -> Fmt.string fmt "incomplete "
    | false -> ()
  in
  let name = Pp_utils.maybe_quote_ident spec.spec_name in
  Fmt.pf fmt "@[<v 2>@[<h>%aspec %s(%a)%a@]@\n%a@]" pp_incomplete
    spec.spec_incomplete name
    Fmt.(list ~sep:comma string)
    spec.spec_params pp_raw_args spec
    Fmt.(list ~sep:semi pp_sspec)
    spec.spec_sspecs

let parameter_types (preds : (string, Pred.t) Hashtbl.t) (spec : t) : t =
  let map_asrts (pred, loc) =
    match Pred.extend_asrt_pred_types preds pred with
    | Ok pred -> (pred, loc)
    | Error msg ->
        raise
          (Gillian_result.Exc.analysis_failure ~in_target:spec.spec_name ?loc
             msg)
  in
  let pt_sspec (sspec : st) : st =
    {
      sspec with
      ss_pre = map_asrts sspec.ss_pre;
      ss_posts = List.map map_asrts sspec.ss_posts;
    }
  in
  { spec with spec_sspecs = List.map pt_sspec spec.spec_sspecs }

let label_vars_to_set lab =
  Option.map (fun (l, vl) -> (l, Containers.SS.of_list vl)) lab

let to_yojson = TypeDef__.spec_to_yojson
let of_yojson = TypeDef__.spec_of_yojson

let hash_of_t (spec : t) =
  Fmt.str "%a" pp spec |> Digest.string |> Digest.to_hex
