(** JSIL Symbolic Heap *)

open Gillian.Gil_syntax
open Javert_utils
module SSubst = Gillian.Symbolic.Subst
module L = Logging

type s_object = (SFVL.t * Expr.t option) * Expr.t option

type t = {
  cfvl : (string, SFVL.t) Hashtbl.t;
  cdom : (string, Expr.t option) Hashtbl.t;
  cmet : (string, Expr.t option) Hashtbl.t;
  sfvl : (string, SFVL.t) Hashtbl.t;
  sdom : (string, Expr.t option) Hashtbl.t;
  smet : (string, Expr.t option) Hashtbl.t;
  cdmn : SS.t ref;
  sdmn : SS.t ref;
  (* Alternative ownership of the complete field/domain footprint. The old
     tables contain only an empty placeholder and separately owned metadata. *)
  ordered : (string, Expr.t * Expr.t) Hashtbl.t;
      [@default (Hashtbl.create 0)]
}
[@@deriving yojson]

(* ************* *
 *  AUXILIARIES  *
 * ************* *)

let is_c = Expr.is_concrete

let merge (a : 't option) (b : 't option) (f : 't -> 't -> 't) : 't option =
  match (a, b) with
  | a, None -> a
  | None, b -> b
  | Some a, Some b -> Some (f a b)

let get_ordered heap loc = Hashtbl.find_opt heap.ordered loc

let require_exposed heap loc =
  if Hashtbl.mem heap.ordered loc then
    raise
      (Gillian.Utils.Gillian_result.Exc.Gillian_error
         (OperationError
            "Unsupported ordered fields: operation requires exposed cells."))

let get_fvl (heap : t) (loc : string) : SFVL.t option =
  require_exposed heap loc;
  let cfvl = Hashtbl.find_opt heap.cfvl loc in
  let sfvl = Hashtbl.find_opt heap.sfvl loc in
  merge cfvl sfvl SFVL.union

let get_dom (heap : t) (loc : string) : Expr.t option =
  let cdom = Option.value ~default:None (Hashtbl.find_opt heap.cdom loc) in
  let sdom = Option.value ~default:None (Hashtbl.find_opt heap.sdom loc) in
  merge cdom sdom (fun _ _ ->
      raise
        (Failure "Domain in both the concrete and symbolic part of the heap."))

let get_met (heap : t) (loc : string) : Expr.t option =
  let cmet = Option.value ~default:None (Hashtbl.find_opt heap.cmet loc) in
  let smet = Option.value ~default:None (Hashtbl.find_opt heap.smet loc) in
  merge cmet smet (fun _ _ ->
      raise
        (Failure "MetaData in both the concrete and symbolic part of the heap."))

let set_fvl (heap : t) (loc : string) (fvl : SFVL.t) : unit =
  require_exposed heap loc;
  Hashtbl.remove heap.cfvl loc;
  Hashtbl.remove heap.sfvl loc;
  heap.cdmn := Var.Set.remove loc !(heap.cdmn);
  heap.sdmn := Var.Set.remove loc !(heap.sdmn);

  let cfvl, sfvl =
    SFVL.partition (fun prop value -> is_c value && is_c prop) fvl
  in
  match (cfvl = SFVL.empty, sfvl = SFVL.empty) with
  | true, true ->
      Hashtbl.replace heap.cfvl loc SFVL.empty;
      Hashtbl.remove heap.sfvl loc;
      heap.cdmn := Var.Set.add loc !(heap.cdmn)
  | true, false ->
      Hashtbl.remove heap.cfvl loc;
      Hashtbl.replace heap.sfvl loc sfvl;
      heap.sdmn := Var.Set.add loc !(heap.sdmn)
  | false, true ->
      Hashtbl.replace heap.cfvl loc cfvl;
      Hashtbl.remove heap.sfvl loc;
      heap.cdmn := Var.Set.add loc !(heap.cdmn)
  | false, false ->
      Hashtbl.replace heap.cfvl loc cfvl;
      Hashtbl.replace heap.sfvl loc sfvl;
      heap.cdmn := Var.Set.add loc !(heap.cdmn);
      heap.sdmn := Var.Set.add loc !(heap.sdmn)

let set_dom (heap : t) (loc : string) (dom : Expr.t option) : unit =
  require_exposed heap loc;
  Hashtbl.remove heap.cdom loc;
  Hashtbl.remove heap.sdom loc;
  let add, rem =
    match dom with
    | Some x when not (is_c x) -> (heap.sdom, heap.cdom)
    | _ -> (heap.cdom, heap.sdom)
  in
  Hashtbl.replace add loc dom;
  Hashtbl.remove rem loc

let set_met (heap : t) (loc : string) (met : Expr.t option) : unit =
  Hashtbl.remove heap.cmet loc;
  Hashtbl.remove heap.smet loc;
  let add, rem =
    match met with
    | Some x when not (is_c x) -> (heap.smet, heap.cmet)
    | _ -> (heap.cmet, heap.smet)
  in
  Hashtbl.replace add loc met;
  Hashtbl.remove rem loc

(*************************************)
(** Symbolic heap functions **)

(*************************************)

(** Returns an empty symbolic heap *)
let init () : t =
  let open Config in
  {
    cfvl = Hashtbl.create big_tbl_size;
    sfvl = Hashtbl.create big_tbl_size;
    cdom = Hashtbl.create big_tbl_size;
    sdom = Hashtbl.create big_tbl_size;
    cmet = Hashtbl.create big_tbl_size;
    smet = Hashtbl.create big_tbl_size;
    cdmn = ref SS.empty;
    sdmn = ref SS.empty;
    ordered = Hashtbl.create big_tbl_size;
  }

(** Symbolic heap read heap(loc) *)
let get (heap : t) (loc : string) : s_object option =
  Option.map
    (fun sfvl -> ((sfvl, get_dom heap loc), get_met heap loc))
    (get_fvl heap loc)

(** Symbolic heap read heap(loc) with the normal new obj default *)
let get_with_default (heap : t) (loc : string) : s_object =
  Option.value ~default:((SFVL.empty, None), None) (get heap loc)

(** Symbolic heap set heap(loc) is assigned to fv_list *)
let set
    (heap : t)
    (loc : string)
    (fv_list : SFVL.t)
    (dom : Expr.t option)
    (metadata : Expr.t option) : unit =
  set_fvl heap loc fv_list;
  set_dom heap loc dom;
  set_met heap loc metadata

(* Called only after the memory producer has checked vacancy. These helpers
   never combine a sequence with a separately owned field/domain fragment. *)
let set_ordered heap loc keys values =
  require_exposed heap loc;
  let fields, domain = fst (get_with_default heap loc) in
  if not (SFVL.is_empty fields) || Option.is_some domain then
    invalid_arg "Ordered fields overlap exposed ownership";
  let metadata = get_met heap loc in
  set heap loc SFVL.empty None metadata;
  Hashtbl.replace heap.ordered loc (keys, values)

let clear_ordered heap loc = Hashtbl.remove heap.ordered loc

(** Symbolic heap put heap (loc, (perm, field)) is assigned to value *)
let set_fv_pair
    ?(abstract = false)
    (heap : t)
    (loc : string)
    (field : Expr.t)
    (value : Expr.t) : unit =
  (* Update the combined object before splitting it: changing a value from
     concrete to symbolic must preserve its property's creation order. *)
  let fields = Option.value ~default:SFVL.empty (get_fvl heap loc) in
  let add = if abstract then SFVL.add_abstract else SFVL.add in
  set_fvl heap loc (add field value fields)

let init_object
    (heap : t)
    (loc : string)
    ?is_empty:(ie = false)
    (mtdt : Expr.t option) : unit =
  if Hashtbl.mem heap.cfvl loc || Hashtbl.mem heap.sfvl loc then
    raise (Failure "Illegal init_object")
  else
    let dom : Expr.t option = if ie then None else Some (ESet []) in
    set heap loc SFVL.empty dom mtdt

let has_loc (heap : t) (loc : string) : bool =
  Hashtbl.mem heap.cfvl loc || Hashtbl.mem heap.sfvl loc

(** Removes the fv-list associated with --loc-- in --heap-- *)
let remove (heap : t) (loc : string) : unit =
  require_exposed heap loc;
  Hashtbl.remove heap.cfvl loc;
  Hashtbl.remove heap.sfvl loc;
  Hashtbl.remove heap.cdom loc;
  Hashtbl.remove heap.sdom loc;
  Hashtbl.remove heap.cmet loc;
  Hashtbl.remove heap.smet loc;
  heap.cdmn := Var.Set.remove loc !(heap.cdmn);
  heap.sdmn := Var.Set.remove loc !(heap.sdmn)

(** Retrieves the domain of --heap-- *)
let domain (heap : t) : SS.t = SS.union !(heap.cdmn) !(heap.sdmn)

let cdomain (heap : t) : SS.t = !(heap.cdmn)

(** Returns a copy of --heap-- *)
let copy (heap : t) : t =
  {
    cfvl = Hashtbl.copy heap.cfvl;
    sfvl = Hashtbl.copy heap.sfvl;
    cdom = Hashtbl.copy heap.cdom;
    sdom = Hashtbl.copy heap.sdom;
    cmet = Hashtbl.copy heap.cmet;
    smet = Hashtbl.copy heap.smet;
    cdmn = ref !(heap.cdmn);
    sdmn = ref !(heap.sdmn);
    ordered = Hashtbl.copy heap.ordered;
  }

let merge_exposed_loc (heap : t) (new_loc : string) (old_loc : string) : unit =
  let domain = domain heap in
  let cfvl, sfvl, dom, met =
    match SS.mem new_loc domain with
    | true ->
        (* Merge field-value lists *)
        let ocvfl, osfvl =
          ( Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.cfvl old_loc),
            Option.value ~default:SFVL.empty
              (Hashtbl.find_opt heap.sfvl old_loc) )
        in
        let ncvfl, nsfvl =
          ( Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.cfvl new_loc),
            Option.value ~default:SFVL.empty
              (Hashtbl.find_opt heap.sfvl new_loc) )
        in
        let cfvl = SFVL.union ncvfl ocvfl in
        let sfvl = SFVL.union nsfvl osfvl in

        (* Merge metadata *)
        let odom = get_dom heap old_loc in
        let ndom = get_dom heap new_loc in
        let dom =
          match (odom, ndom) with
          | None, None -> None
          | None, Some dom | Some dom, None -> Some dom
          | Some dom1, Some dom2 -> Some (NOp (SetUnion, [ dom1; dom2 ]))
        in

        let omet = get_met heap old_loc in
        let nmet = get_met heap new_loc in
        let met =
          match (omet, nmet) with
          | None, None -> None
          | None, Some met | Some met, None -> Some met
          | Some met1, Some _ -> Some met1
        in

        (cfvl, sfvl, dom, met)
    | false ->
        ( Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.cfvl old_loc),
          Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.sfvl old_loc),
          get_dom heap old_loc,
          get_met heap old_loc )
  in
  set_fvl heap new_loc (SFVL.union cfvl sfvl);
  set_dom heap new_loc dom;
  set_met heap new_loc met;
  remove heap old_loc

let merge_loc heap new_loc old_loc =
  if new_loc <> old_loc then
    match (get_ordered heap old_loc, get_ordered heap new_loc) with
    | None, None -> merge_exposed_loc heap new_loc old_loc
    | Some _, Some _ ->
        raise (Gillian.Utils.Exceptions.Unsupported
                 "Ordered fields overlap after location substitution")
    | old_ordered, new_ordered ->
        let exposed = if Option.is_some old_ordered then new_loc else old_loc in
        let fields, domain = fst (get_with_default heap exposed) in
        if not (SFVL.is_empty fields) || Option.is_some domain then
          raise (Gillian.Utils.Exceptions.Unsupported
                   "Ordered fields overlap after location substitution");
        let metadata =
          match (get_met heap old_loc, get_met heap new_loc) with
          | Some a, Some b when a <> b ->
              raise (Gillian.Utils.Exceptions.Unsupported
                       "Ordered fields have unresolved metadata aliases")
          | Some a, _ | _, Some a -> Some a
          | None, None -> None
        in
        let keys, values = Option.get (merge old_ordered new_ordered (fun _ _ -> assert false)) in
        clear_ordered heap old_loc;
        clear_ordered heap new_loc;
        remove heap old_loc;
        set heap new_loc SFVL.empty None metadata;
        set_ordered heap new_loc keys values

(** Modifies --heap-- in place updating it to subst(heap) *)
let substitution_in_place (subst : SSubst.t) (heap : t) : unit =
  (* If the substitution is empty, there is nothing to be done *)
  if not (SSubst.domain subst None = Expr.Set.empty) then (
    (* The substitution is not empty *)
    let le_subst = SSubst.subst_in_expr subst ~partial:true in

    (*
      L.(verbose (fun m -> m "CFVL: %d" (Hashtbl.length heap.cfvl)));
      L.(verbose (fun m -> m "SFVL: %d" (Hashtbl.length heap.sfvl)));
      L.(verbose (fun m -> m "CDOM: %d" (Hashtbl.length heap.cdom)));
      L.(verbose (fun m -> m "SDOM: %d" (Hashtbl.length heap.sdom)));
      L.(verbose (fun m -> m "CMET: %d" (Hashtbl.length heap.cmet)));
      L.(verbose (fun m -> m "SMET: %d" (Hashtbl.length heap.smet)));
    *)

    Hashtbl.filter_map_inplace
      (fun _ (keys, values) -> Some (le_subst keys, le_subst values))
      heap.ordered;

    (* Field-value lists *)
    Hashtbl.iter
      (fun loc fvl ->
        (* Substitute *)
        let fvl = SFVL.substitution subst true fvl in
        (* Partition into concrete and symbolic *)
        let cfvl, sfvl =
          SFVL.partition (fun prop value -> is_c value && is_c prop) fvl
        in
        (* Set symbolic *)
        Hashtbl.replace heap.sfvl loc sfvl;
        (* Merge concrete with new value taking precedence *)
        let prev_cfvl =
          Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.cfvl loc)
        in
        Hashtbl.replace heap.cfvl loc (SFVL.union cfvl prev_cfvl))
      heap.sfvl;

    (* Domain table *)
    Hashtbl.iter
      (fun loc dom ->
        (* Substitute *)
        let dom = Option.map le_subst dom in
        (* Set domain *)
        set_dom heap loc dom)
      heap.sdom;

    (* Metadata table *)
    Hashtbl.iter
      (fun loc met ->
        (* Substitute *)
        let met = Option.map le_subst met in
        (* Set domain *)
        set_met heap loc met)
      heap.smet;

    (* Now we need to deal with any substitutions in the locations themselves *)
    let aloc_subst =
      SSubst.filter subst (fun var _ ->
          match var with
          | ALoc _ -> true
          | _ -> false)
    in
    SSubst.iter aloc_subst (fun aloc new_loc ->
        let aloc =
          match aloc with
          | ALoc loc -> loc
          | _ -> raise (Failure "Impossible by construction")
        in
        let new_loc =
          match (new_loc : Expr.t) with
          | Lit (Loc loc) -> loc
          | ALoc loc -> loc
          | _ ->
              raise
                (Failure
                   (Printf.sprintf "Heap substitution fail for loc: %s"
                      ((Fmt.to_to_string Expr.pp) new_loc)))
        in
        merge_loc heap new_loc aloc))

(** Returns the serialization of --heap-- as a list *)
let to_list (heap : t) : (string * s_object) list =
  let domain = domain heap in
  SS.fold (fun loc ac -> (loc, Option.get (get heap loc)) :: ac) domain []

(** converts a symbolic heap to a list of assertions *)
let assertions (heap : t) : Asrt.t =
  let make_loc_lexpr loc =
    if Names.is_aloc_name loc then Expr.ALoc loc else Expr.Lit (Loc loc)
  in

  let assertions_of_object (loc, ((fv_list, domain), metadata)) =
    let le_loc = make_loc_lexpr loc in
    (* A loop frame is restored from these assertions. Exporting only Cell
       assertions would discard recorded insertion order. OrderedFields can
       replace the whole field/domain footprint, but never a partial one.
       This exporter has no pure context: require syntactic completeness,
       distinct concrete names and definitely present values. Otherwise keep
       the conservative cell representation; do not manufacture a witness. *)
    let ordered =
      let names = SFVL.field_names fv_list in
      let complete =
        match domain with
        | Some (Expr.ESet domain) ->
            Expr.Set.equal (Expr.Set.of_list domain) (Expr.Set.of_list names)
        | _ -> false
      in
      let rec distinct_names seen = function
        | [] -> true
        | name :: rest -> (
            let key =
              match name with
              | Expr.Lit (Literal.String s) -> Some s
              | Expr.Lit (Literal.Utf16String s) ->
                  Some (Gillian.Utils.Utf16.to_canonical s)
              | _ -> None
            in
            match key with
            | Some s when not (SS.mem s seen) ->
                distinct_names (SS.add s seen) rest
            | _ -> false)
      in
      let present, _ =
        SFVL.partition (fun _ value -> value <> Expr.Lit Literal.Nono) fv_list
      in
      let definitely_present =
        SFVL.fold
          (fun _ value ok ->
            ok
            &&
            match value with
            | Expr.Lit Literal.Nono -> false
            | Expr.Lit _ | Expr.ALoc _ | Expr.EList _ | Expr.ESet _ -> true
            | _ -> false)
          present true
      in
      if complete && distinct_names SS.empty names && definitely_present then
        try
          let keys = SFVL.ordered_field_names present in
          let values =
            List.map (fun key -> Option.get (SFVL.get key present)) keys
          in
          Some
            (Asrt.CorePred
               ( Javert_utils.JSILNames.aOrderedFields,
                 [ le_loc ],
                 [ Expr.EList keys; Expr.EList values ] ))
        with
        | Gillian.Utils.Gillian_result.Exc.Gillian_error (OperationError _)
        | Gillian.Utils.Exceptions.Unsupported _
        ->
          None
      else None
    in
    let fields_and_domain =
      match ordered with
      | Some resource -> [ resource ]
      | None ->
          SFVL.assertions le_loc fv_list
          @ Option.fold
              ~some:(fun domain ->
                [ Asrt_utils.empty_fields ~loc:le_loc ~domain ])
              ~none:[] domain
    in
    let metadata =
      match metadata with
      | Some metadata -> [ Asrt_utils.metadata ~loc:le_loc ~metadata ]
      | None -> []
    in
    fields_and_domain @ metadata
  in

  let exposed =
    SS.elements (domain heap)
    |> List.filter (fun loc -> not (Hashtbl.mem heap.ordered loc))
    |> List.map (fun loc -> (loc, Option.get (get heap loc)))
    |> List.concat_map assertions_of_object
  in
  let ordered =
    Hashtbl.fold
      (fun loc (keys, values) acc ->
        let loc_expr = make_loc_lexpr loc in
        let metadata =
          Option.fold ~none:[]
            ~some:(fun metadata -> [ Asrt_utils.metadata ~loc:loc_expr ~metadata ])
            (get_met heap loc)
        in
        Asrt.CorePred (Javert_utils.JSILNames.aOrderedFields,
                      [ loc_expr ], [ keys; values ]) :: metadata @ acc)
      heap.ordered []
  in
  List.sort Asrt.compare (exposed @ ordered)

let wf_assertions_of_obj (heap : t) (loc : string) : Expr.t list =
  let cfvl =
    Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.cfvl loc)
  in
  let sfvl =
    Option.value ~default:SFVL.empty (Hashtbl.find_opt heap.sfvl loc)
  in
  let cpps = SFVL.field_names cfvl in
  let spps = SFVL.field_names sfvl in
  let props = List_utils.cross_product spps (cpps @ spps) (fun x y -> (x, y)) in
  let props = List.filter (fun (x, y) -> x <> y) props in
  List.map (fun (x, y) : Expr.t -> UnOp (Not, BinOp (x, Equal, y))) props

let wf_assertions (heap : t) : Expr.t list =
  let domain = domain heap in
  SS.fold (fun loc ac -> wf_assertions_of_obj heap loc @ ac) domain []

let is_well_formed (heap : t) : unit =
  Hashtbl.iter
    (fun loc _ ->
      let fields table = Option.value ~default:SFVL.empty (Hashtbl.find_opt table loc) in
      if not (SFVL.is_empty (fields heap.cfvl))
         || not (SFVL.is_empty (fields heap.sfvl)) || Option.is_some (get_dom heap loc)
      then invalid_arg "Ordered fields coexist with exposed ownership")
    heap.ordered;
  let cfvl =
    Hashtbl.fold
      (fun _ fvl ac ->
        SFVL.fold (fun prop value ac -> ac && is_c prop && is_c value) fvl ac)
      heap.cfvl true
  in
  if not cfvl then raise (Failure "Symbolicness in concrete part of the heap");
  let sfvl =
    Hashtbl.fold
      (fun _ fvl ac ->
        SFVL.fold
          (fun prop value ac -> ac && ((not (is_c prop)) || not (is_c value)))
          fvl ac)
      heap.sfvl true
  in
  if not sfvl then
    raise (Failure "Concreteness in the symbolic part of the heap");
  let dom_kept = domain heap in
  let dom_calc_1 =
    SS.union
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cfvl SS.empty)
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.sfvl SS.empty)
  in
  let dom_calc_2 =
    SS.union
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cdom SS.empty)
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.sdom SS.empty)
  in
  let dom_calc_3 =
    SS.union
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.cmet SS.empty)
      (Hashtbl.fold (fun v _ ac -> SS.add v ac) heap.smet SS.empty)
  in
  let dom_calc = SS.union dom_calc_1 (SS.union dom_calc_2 dom_calc_3) in
  if SS.elements dom_kept <> SS.elements dom_calc then
    let msg =
      Printf.sprintf "Domain mismatch:\n%s\n%s"
        (String.concat ", " (SS.elements dom_kept))
        (String.concat ", " (SS.elements dom_calc))
    in
    L.fail msg

let pp_locations locs ft heap =
  let pp_one ft loc =
    match get_ordered heap loc with
    | Some (keys, values) ->
        Fmt.pf ft "@[%s |-> OrderedFields(%a; %a) with metadata %a@]"
          loc Expr.pp keys Expr.pp values Fmt.(option Expr.pp) (get_met heap loc)
    | None ->
        let (fields, domain), metadata = get_with_default heap loc in
        Fmt.pf ft "@[%s |-> [ @[%a@] | @[%a@] ] with metadata %a@]"
          loc SFVL.pp fields Fmt.(option Expr.pp) domain
          Fmt.(option ~none:(any "unknown") Expr.pp) metadata
  in
  Fmt.(list ~sep:(any "@\n") pp_one) ft (SS.elements locs)

let pp ft heap = pp_locations (domain heap) ft heap

let get_print_info locs heap =
  let domain = domain heap in
  let metadata_locs =
    SS.fold
      (fun loc locs ->
        match get_met heap loc with
        | (Some (Lit (Loc x)) | Some (ALoc x)) when SS.mem x domain ->
            SS.add x locs
        | _ -> locs)
      locs SS.empty
  in
  (* TODO: Traverse locations and collect info about other locations and lvars *)
  (SS.empty, metadata_locs)

let pp_by_need locs ft heap =
  pp_locations (SS.inter locs (domain heap)) ft heap

let get_inv_metadata (heap : t) : (Expr.t, Expr.t) Hashtbl.t =
  let inv_metadata = Hashtbl.create Config.medium_tbl_size in
  let traverse_metadata_table mt : unit =
    Hashtbl.iter
      (fun loc e_metadata ->
        match e_metadata with
        | None -> ()
        | Some e_metadata ->
            let loc_e =
              if Names.is_lloc_name loc then Expr.Lit (Loc loc) else ALoc loc
            in
            Hashtbl.add inv_metadata e_metadata loc_e)
      mt
  in
  traverse_metadata_table heap.smet;
  traverse_metadata_table heap.cmet;
  inv_metadata

let clean_up (heap : t) : unit =
  SS.iter
    (fun loc ->
      match has_loc heap loc && not (Hashtbl.mem heap.ordered loc) with
      | false -> ()
      | true -> (
          let (fvl, dom), met = get_with_default heap loc in
          match (fvl = SFVL.empty, dom) with
          | true, None -> (
              remove heap loc;
              match met with
              | Some (ALoc loc) | Some (Lit (Loc loc)) -> remove heap loc
              | _ -> ())
          | _, _ -> ()))
    (domain heap)

let lvars (heap : t) : Var.Set.t =
  let lvars_fvl =
    Hashtbl.fold
      (fun _ fvl ac -> Var.Set.union (SFVL.lvars fvl) ac)
      heap.sfvl Var.Set.empty
  in
  let lvars_dom =
    Hashtbl.fold
      (fun _ oe ac ->
        let voe = Option.fold ~some:Expr.lvars ~none:Var.Set.empty oe in
        Var.Set.union voe ac)
      heap.sdom Var.Set.empty
  in
  let lvars_met =
    Hashtbl.fold
      (fun _ oe ac ->
        let voe = Option.fold ~some:Expr.lvars ~none:Var.Set.empty oe in
        Var.Set.union voe ac)
      heap.smet Var.Set.empty
  in
  Hashtbl.fold
    (fun _ (keys, values) acc -> SS.union acc (SS.union (Expr.lvars keys) (Expr.lvars values)))
    heap.ordered
    (List.fold_left SS.union Var.Set.empty [ lvars_fvl; lvars_met; lvars_dom ])

let exposed_alocs (heap : t) : Var.Set.t =
  let union = Var.Set.union in
  Var.Set.empty
  |> Hashtbl.fold (fun _ fvl ac -> Var.Set.union (SFVL.alocs fvl) ac) heap.sfvl
  |> Hashtbl.fold
       (fun _ oe ac ->
         Option.fold ~some:(fun oe -> union (Expr.alocs oe) ac) ~none:ac oe)
       heap.sdom
  |> Hashtbl.fold
       (fun _ oe ac ->
         Option.fold ~some:(fun oe -> union (Expr.alocs oe) ac) ~none:ac oe)
       heap.smet

(* Include variables hidden in the whole-field alternative in freshness and
   substitution accounting; omission would make framing unsound. *)
let alocs heap =
  Hashtbl.fold
    (fun _ (keys, values) acc -> SS.union acc (SS.union (Expr.alocs keys) (Expr.alocs values)))
    heap.ordered (exposed_alocs heap)
