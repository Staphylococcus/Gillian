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
  spec_params : string list;  (** Procedure/spec parameters *)
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
    spec_sspecs;
    spec_normalised;
    spec_incomplete;
    spec_to_verify;
    spec_location;
  }

let extend (spec : t) (sspecs : st list) : t =
  { spec with spec_sspecs = sspecs @ spec.spec_sspecs }

let get_params (spec : t) : string list = spec.spec_params

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
  Fmt.pf fmt "@[<v 2>@[<h>%aspec %s(%a)@]@\n%a@]" pp_incomplete
    spec.spec_incomplete name
    Fmt.(list ~sep:comma string)
    spec.spec_params
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
