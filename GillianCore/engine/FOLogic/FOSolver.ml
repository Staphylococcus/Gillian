open SVal
module L = Logging

(** **************** * SATISFIABILITY * * **************** **)

let get_axioms (fs : Expr.Set.t) (_ : Type_env.t) : Expr.Set.t =
  Expr.Set.fold
    (fun (pf : Expr.t) (result : Expr.Set.t) ->
      match pf with
      | BinOp (NOp (LstCat, x), Equal, NOp (LstCat, y)) ->
          Expr.Set.add
            (Reduction.reduce_lexpr
               (BinOp
                  ( UnOp (LstLen, NOp (LstCat, x)),
                    Equal,
                    UnOp (LstLen, NOp (LstCat, y)) )))
            result
      | _ -> result)
    fs Expr.Set.empty

let simplify_pfs_and_gamma
    ?(matching = false)
    ?relevant_info
    (fs : Expr.t list)
    (gamma : Type_env.t) : Expr.Set.t * Type_env.t * SESubst.t =
  let pfs, gamma =
    match (relevant_info, !Config.under_approximation) with
    | Some relevant_info, false ->
        let pfs = PFS.filter_with_info relevant_info (PFS.of_list fs) in
        (* Formula relevance is transitive. Preserve the existing types of every
           variable in the retained formulas, not only the initial query roots.
           Otherwise a retained Boolean can become an unconstrained value, and
           known Number operands acquire expensive generic SMT encodings. *)
        let pvars, lvars, locs = relevant_info in
        let names =
          PFS.fold_left
            (fun names pf ->
              SS.union names
                (SS.union (Expr.pvars pf)
                   (SS.union (Expr.lvars pf) (Expr.locs pf))))
            (SS.union pvars (SS.union lvars locs))
            pfs
        in
        (pfs, Type_env.filter_vars gamma names)
    | _ -> (PFS.of_list fs, Type_env.copy gamma)
  in
  let subst, _ = Simplifications.simplify_pfs_and_gamma ~matching pfs gamma in
  let fs_lst = PFS.to_list pfs in
  let fs_set = Expr.Set.of_list fs_lst in
  (fs_set, gamma, subst)

let check_satisfiability_with_model (fs : Expr.t list) (gamma : Type_env.t) :
    SESubst.t option =
  Smt.with_native_smt_context
    (fun () ->
      `Assoc
          [ ("operation", `String "satisfiability-with-model");
            ("original_fs", `List (List.map (fun e -> `String (Fmt.str "%a" Expr.pp e)) fs));
            ("original_gamma", `String (Fmt.str "%a" Type_env.pp gamma)) ])
    (fun () ->
    let fs, gamma, subst = simplify_pfs_and_gamma fs gamma in
    let gamma_tbl = Type_env.as_hashtbl gamma in
    let model = Smt.check_sat fs gamma_tbl in
    let lvars =
      List.fold_left
        (fun ac vs ->
          let vs =
            Expr.Set.of_list (List.map (fun x -> Expr.LVar x) (SS.elements vs))
          in
          Expr.Set.union ac vs)
        Expr.Set.empty
        (List.map Expr.lvars (Expr.Set.elements fs))
    in
    let smt_vars = Expr.Set.diff lvars (SESubst.domain subst None) in
    L.(
      verbose (fun m ->
          m "OBTAINED VARS: %s\n"
            (String.concat ", "
               (List.map
                  (fun e -> Format.asprintf "%a" Expr.pp e)
                  (Expr.Set.elements smt_vars)))));
    let update x e = SESubst.put subst (LVar x) e in
    match model with
    | None -> None
    | Some model -> (
        try
          Smt.lift_model model gamma_tbl update smt_vars;
          Some subst
        with e ->
          let () =
            L.verbose (fun m ->
                m "Error when attempting to get SMT model: %s"
                  (Printexc.to_string e))
          in
          None)
    )

(* Boolean SAT only: existentially split one isolated high-index UTF16 read.
   With 0 <= k < N, xs[k] = item is equivalent to xs = pre ++ [item] ++ post,
   len(pre) = k. Every observation of xs must be one of the same-index aliases
   or a literal length comparison; otherwise retain the complete old query.
   Eliminating xs from this closed fragment leaves only prefix/suffix lengths.
   The equivalence holds for the formulas retained after either matching-mode
   simplification. The matching flag still controls that original simplification
   and its native context. No model for the eliminated original List is returned
   or cached under its old formula key; the model-returning API is unchanged. *)
let compact_literal_nth_satisfiability ~matching:(_ : bool) fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None
  else
    let alias = function
      | Expr.BinOp
          (Expr.LVar item, ((Equal | ValueEqual) as equality),
           Expr.BinOp (Expr.LVar xs, LstNth, Expr.Lit (Int k)))
      | Expr.BinOp
          (Expr.BinOp (Expr.LVar xs, LstNth, Expr.Lit (Int k)),
           ((Equal | ValueEqual) as equality), Expr.LVar item)
        when Type_env.get gamma xs = Some Type.ListType
             && Type_env.get gamma item = Some Type.Utf16Type
             && Z.gt k (Z.of_int 100) -> Some (xs,k,item,equality)
      | _ -> None
    in
    let aliases = List.filter_map alias (Expr.Set.elements fs) in
    let roles = List.map (fun (xs,k,_,_) -> xs,k) aliases
      |> List.sort_uniq Stdlib.compare in
    match roles, aliases with
    | [(xs,k)], (_,_,item,_) :: _ ->
        let length = Expr.UnOp (LstLen, Expr.LVar xs) in
        let length_atom = function
          | Expr.BinOp
              (left, ((Equal | ValueEqual | ILessThan | ILessThanEqual) as op),
               (Expr.Lit (Int _) as right)) when Expr.equal left length ->
              Some (left,op,right)
          | Expr.BinOp
              ((Expr.Lit (Int _) as left),
               ((Equal | ValueEqual | ILessThan | ILessThanEqual) as op), right)
            when Expr.equal right length -> Some (left,op,right)
          | _ -> None
        in
        let exact_lengths = Expr.Set.fold (fun e ns ->
          match length_atom e with
          | Some (Expr.UnOp (LstLen,_), (Equal | ValueEqual), Expr.Lit (Int n))
          | Some (Expr.Lit (Int n), (Equal | ValueEqual), Expr.UnOp (LstLen,_)) -> n::ns
          | _ -> ns) fs [] |> List.sort_uniq Z.compare in
        let permitted e =
          if not (SS.mem xs (Expr.lvars e)) then true
          else match alias e with
            | Some (ys,j,_,_) -> ys = xs && Z.equal j k
            | None -> Option.is_some (length_atom e)
        in
        (match exact_lengths with
         | [n] when Z.lt k n && Z.leq n (Z.of_int max_int)
                    && Expr.Set.for_all permitted fs ->
             let used = ref (Expr.Set.fold (fun e names -> SS.union (Expr.lvars e) names)
               fs SS.empty) in
             let rec fresh () =
               let name = LVar.alloc () in
               if SS.mem name !used || Type_env.mem gamma name then fresh ()
               else (used := SS.add name !used; name) in
             let prefix = fresh () and suffix = fresh () in
             let plen = Expr.UnOp (LstLen, Expr.LVar prefix)
             and slen = Expr.UnOp (LstLen, Expr.LVar suffix) in
             let replacement_length =
               Expr.BinOp (Expr.BinOp (plen,IPlus,Expr.int 1),IPlus,slen) in
             let replacement e = if Expr.equal e length then replacement_length else e in
             let projected = Expr.Set.fold (fun e acc ->
               let e = match alias e, length_atom e with
                 | Some (ys,j,other,equality), _ when ys = xs && Z.equal j k ->
                     Expr.BinOp (Expr.LVar other,equality,Expr.LVar item)
                 | _, Some (left,op,right) ->
                     Expr.BinOp (replacement left,op,replacement right)
                 | _ -> e in
               Expr.Set.add e acc) fs Expr.Set.empty in
             let projected = List.fold_left (fun acc e -> Expr.Set.add e acc)
               projected [Expr.BinOp (plen,Equal,Expr.Lit (Int k));
                 Expr.BinOp (Expr.int 0,ILessThanEqual,plen);
                 Expr.BinOp (Expr.int 0,ILessThanEqual,slen)] in
             let projected_gamma = Type_env.copy gamma in
             Type_env.update projected_gamma prefix Type.ListType;
             Type_env.update projected_gamma suffix Type.ListType;
             Some (projected,projected_gamma)
         | _ -> None)
    | _ -> None

(* Boolean SAT only. For definitely Number operands, ordinary Equal is fp.eq.
   A positive certificate and finite upper bound exclude NaN, infinities and both
   zeros; equal operands then have identical bits, hence identical formatting.
   License from the original FS/Gamma AND retain the same premises in the copied
   simplified query. Only a surviving original formatter equality (or its Equal
   symmetry) licenses one additional ValueEqual, never atom removal. Thus all
   formatter-attached encoding facts survive. State facts, model-returning SAT
   and entailment stay unchanged; the existing native SAT API decides. *)
let positive_finite_numeric_identity_satisfiability
    original_fs original_gamma fs gamma =
  if not !Config.Verification.total || !Config.under_approximation then None
  else
    let rec number types = function
      | Expr.LVar name -> Type_env.get types name = Some Type.NumberType
      | Expr.Lit (Num _) -> true
      | Expr.BinOp (a, (FPlus | FMinus), b) ->
          number types a && number types b
      | _ -> false
    in
    let numeric_equality a b = function
      | Expr.BinOp (x, Equal, y) ->
          (Expr.equal a x && Expr.equal b y)
          || (Expr.equal a y && Expr.equal b x)
      | _ -> false
    in
    let query_fs = Expr.Set.elements fs in
    let bounded_positive value =
      (* Concrete zero/nonfinite operands cannot witness this positive branch. *)
      let eligible = match value with
        | Expr.Lit (Num n) -> Float.is_finite n && n > 0.
        | _ -> true in
      if not eligible then None else
      let positive = List.find_opt (function
        | Expr.BinOp (Expr.Lit (Num z), FLessThan, x) as atom ->
            z = 0. && Expr.equal value x && Expr.Set.mem atom fs
        | _ -> false) original_fs in
      let positive = match positive with
        | Some atom -> Some [atom]
        | None ->
            let nonnegative = List.find_opt (function
              | Expr.BinOp (Expr.Lit (Num z), FLessThanEqual, x) as atom ->
                  z = 0. && Expr.equal value x && Expr.Set.mem atom fs
              | _ -> false) original_fs in
            (* Numeric Equal identifies BOTH zeros. A negated ValueEqual to
               one zero does not, so it cannot license this certificate. Every
               selected atom must be original and still present in the query. *)
            let nonzero = List.find_opt (function
              | (Expr.UnOp (Not, BinOp (x, Equal, Lit (Num z))) as atom)
              | (Expr.UnOp (Not, BinOp (Lit (Num z), Equal, x)) as atom) ->
                  z = 0. && Expr.equal value x && Expr.Set.mem atom fs
              | _ -> false) original_fs in
            (match nonnegative, nonzero with
             | Some lower, Some nonzero -> Some [lower;nonzero]
             | _ -> None)
      in
      let upper = List.find_opt (function
        | Expr.BinOp (x, FLessThanEqual, Expr.Lit (Num n)) as atom ->
            Expr.equal value x && Float.is_finite n && Expr.Set.mem atom fs
        | _ -> false) original_fs in
      match positive, upper with
      | Some premises, Some u -> Some (premises @ [u])
      | _ -> None
    in
    let licensed = List.find_map (function
      | Expr.BinOp
          ((Expr.UnOp (NumberToUtf16, a) as left), Equal,
           (Expr.UnOp (NumberToUtf16, b) as right)) as original
        when number original_gamma a && number original_gamma b
             && number gamma a && number gamma b ->
          let actual =
            if Expr.Set.mem original fs then Some original
            else let symmetric = Expr.BinOp (right, Equal, left) in
              if Expr.Set.mem symmetric fs then Some symmetric else None in
          let old_equal = List.find_opt (numeric_equality a b) original_fs
          and now_equal = List.find_opt (numeric_equality a b) query_fs in
          let bounds = match bounded_positive a with
            | Some _ as found -> found | None -> bounded_positive b in
          (match actual, old_equal, now_equal, bounds with
           | Some actual, Some old_equal, Some now_equal, Some bounds ->
               let identity = Expr.BinOp (a, ValueEqual, b)
               and symmetric_identity = Expr.BinOp (b, ValueEqual, a) in
               if Expr.Set.mem identity fs || Expr.Set.mem symmetric_identity fs
               then None
               else Some (original,actual,identity,old_equal :: bounds,now_equal :: bounds)
           | _ -> None)
      | _ -> None) original_fs in
    match licensed with
    | None -> None
    | Some (original,actual,identity,old_premises,premises) ->
        (* Positive finite fp.eq has one IEEE value representation.  Add that
           implied identity but retain every original formula and formatter
           term: encoding those terms also emits roundtrip/decimal facts. *)
        Some (Expr.Set.add identity fs, [identity], [original], [actual],
          old_premises, premises)

(* A sufficient contradiction consists only of two retained original atoms.
   Selection is not a proof: native UNSAT is required with the complete current
   Gamma, and every inconclusive result retains the full required query. *)
let finite_number_bound_pair ~original_fs ~original_gamma formulae gamma goal =
  let operand = match goal with
    | Expr.UnOp (Not, BinOp (Lit (Num lower), FLessThanEqual,
        (LVar name as value))) when lower = -. Float.max_float -> Some (name,value)
    | Expr.UnOp (Not, BinOp ((LVar name as value), FLessThanEqual,
        Lit (Num upper))) when upper = Float.max_float -> Some (name,value)
    | _ -> None in
  match operand with
  | Some (name,value)
    when Hashtbl.find_opt original_gamma name = Some Type.NumberType
      && Hashtbl.find_opt gamma name = Some Type.NumberType ->
      let core = Expr.Set.of_list [goal;Expr.UnOp (IsInt,value)] in
      if Expr.Set.cardinal core = 2 && Expr.Set.subset core original_fs
         && Expr.Set.subset core formulae && not (Expr.Set.equal core formulae)
      then Some core else None
  | _ -> None

let check_satisfiability
    ?(matching = false)
    ?time:_
    ?relevant_info
    (fs : Expr.t list)
    (gamma : Type_env.t) : bool =
  Smt.with_native_smt_context
    (fun () ->
      `Assoc
          [ ("operation", `String "satisfiability");
            ("matching", `Bool matching);
            ("original_fs", `List (List.map (fun e -> `String (Fmt.str "%a" Expr.pp e)) fs));
            ("original_gamma", `String (Fmt.str "%a" Type_env.pp gamma)) ])
    (fun () ->
    (* let t = if time = "" then 0. else Unix.gettimeofday () in *)
    L.verbose (fun m -> m "Entering FOSolver.check_satisfiability");
    let original_fs = fs and original_gamma = gamma in
    let fs, gamma, _ = simplify_pfs_and_gamma ?relevant_info ~matching fs gamma in
    let axioms = get_axioms fs gamma in
    let fs = Expr.Set.union fs axioms in
    if Expr.Set.is_empty fs then true
    else if Expr.Set.mem Expr.false_ fs then false
    else
      let result =
        try
          let solve fs =
            match compact_literal_nth_satisfiability ~matching fs gamma with
            | None -> Smt.is_sat fs (Type_env.as_hashtbl gamma)
            | Some (projected,projected_gamma) ->
                Smt.with_native_smt_context
                  (fun () -> `Assoc [
                    ("operation", `String "compact-literal-nth-satisfiability");
                    ("original_fs", `List (List.map
                      (fun e -> `String (Fmt.str "%a" Expr.pp e))
                      (Expr.Set.elements fs)));
                    ("original_gamma", `String (Fmt.str "%a" Type_env.pp gamma)) ])
                  (fun () -> Smt.is_sat projected (Type_env.as_hashtbl projected_gamma))
          in
          let finite_core =
            if not !Config.Verification.total || !Config.under_approximation
               || matching then None
            else
              let originals = Expr.Set.of_list original_fs in
              List.find_map
                (finite_number_bound_pair ~original_fs:originals
                   ~original_gamma:(Type_env.as_hashtbl original_gamma)
                   fs (Type_env.as_hashtbl gamma))
                (Expr.Set.elements fs)
          in
          if (match finite_core with
            | None -> false
            | Some core -> Smt.with_native_smt_context
                (fun () -> `Assoc [
                  ("operation", `String "finite-number-bound-satisfiability-core");
                  ("original_core", `List (List.map Expr.to_yojson (Expr.Set.elements core)));
                  ("query_gamma_bindings", `List
                    (Hashtbl.fold (fun name typ rows ->
                      `List [`String name; `String (Type.str typ)] :: rows)
                      (Type_env.as_hashtbl gamma) [] |> List.sort Stdlib.compare)) ])
                (fun () -> Smt.proves_unsat
                  ~caller_kind:"optional-satisfiability-finite-number-bound-core"
                  core (Type_env.as_hashtbl gamma)))
          then false
          else match positive_finite_numeric_identity_satisfiability
              original_fs original_gamma fs gamma with
          | None -> solve fs
          | Some (projected,added,original_formatters,formatters,old_premises,premises) ->
              let expressions xs = `List (List.map
                (fun e -> `String (Fmt.str "%a" Expr.pp e)) xs) in
              Smt.with_native_smt_context
                (fun () -> `Assoc [
                  ("operation", `String "positive-finite-numeric-identity-satisfiability");
                  ("original_fs", expressions original_fs);
                  ("original_gamma", `String (Fmt.str "%a" Type_env.pp original_gamma));
                  ("added_implied_facts", expressions added);
                  ("original_formatter_atoms", expressions original_formatters);
                  ("retained_query_formatter_atoms", expressions formatters);
                  ("original_premises", expressions old_premises);
                  ("retained_query_premises", expressions premises);
                  ("simplified_fs", expressions (Expr.Set.elements fs));
                  ("projected_fs", expressions (Expr.Set.elements projected)) ])
                (fun () -> solve projected)
        with Smt.SMT_error _ | Smt.SMT_unknown ->
          if !Config.under_approximation then false else raise Smt.SMT_unknown
      in
      (* if time <> "" then
         Utils.Statistics.update_statistics ("FOS: CheckSat: " ^ time)
           (Unix.gettimeofday () -. t); *)
      result
    )

let sat ~matching ~pfs ~gamma formula : bool =
  Smt.with_native_smt_context
    (fun () ->
      `Assoc
          [ ("operation", `String "sat");
            ("matching", `Bool matching);
            ("original_formula", `String (Fmt.str "%a" Expr.pp formula));
            ("original_pfs", `List (List.map (fun e -> `String (Fmt.str "%a" Expr.pp e)) (PFS.to_list pfs)));
            ("original_gamma", `String (Fmt.str "%a" Type_env.pp gamma)) ])
    (fun () ->
    let formula' = Reduction.reduce_lexpr ~matching ~pfs ~gamma formula in
    match formula' with
    | Lit (Bool b) ->
        Logging.verbose (fun fmt ->
            fmt "Discharged sat before SMT @[%a -> %b@]" Expr.pp formula b);
        b
    | _ ->
        let relevant_info =
          (Expr.pvars formula', Expr.lvars formula', Expr.locs formula')
        in
        check_satisfiability ~matching ~relevant_info
          (formula' :: PFS.to_list pfs)
          gamma
    )

(** ************ * ENTAILMENT * * ************ **)

(* Original integer order facts can retain a count alias and its bound while
   omitting unrelated descriptor/string constraints. This is only a weaker
   native UNSAT query: no fact, integer witness or bound is manufactured. *)
let integer_order_core formulae gamma goal =
  let typed name typ = Hashtbl.find_opt gamma name = Some typ in
  let observes_scan =
    let found = ref false in
    let visitor =
      object
        inherit [_] Visitors.iter as super
        method! visit_expr () e =
          (match e with BinOp (_, KeyInsertIndex, _) -> found := true | _ -> ());
          super#visit_expr () e
      end
    in
    visitor#visit_expr () goal;
    !found
  in
  let rec key = function
    | Expr.Lit (Utf16String _) -> true
    | LVar name -> typed name Type.Utf16Type
    | UnOp (NumberToUtf16, LVar name) -> typed name Type.NumberType
    | _ -> false
  and keys = function
    | Expr.LVar name as e ->
        typed name Type.ListType
        && Expr.Set.mem (Expr.UnOp (LstAllUtf16, e)) formulae
    | EList xs -> List.for_all key xs
    | NOp (LstCat, xs) -> List.for_all keys xs
    | _ -> false
  in
  let rec integer = function
    | Expr.Lit (Int _) -> true
    | LVar name -> typed name Type.IntType
    | UnOp (LstLen, LVar name) -> typed name Type.ListType
    | UnOp (NumToInt, (LVar name as n)) ->
        typed name Type.NumberType
        && Expr.Set.mem (Expr.UnOp (IsInt, n)) formulae
    | BinOp (a, (IPlus | IMinus), b) -> integer a && integer b
    | BinOp (xs, KeyInsertIndex, k) -> observes_scan && keys xs && key k
    | _ -> false
  in
  let rec order = function
    | Expr.BinOp (a, (Equal | ILessThan | ILessThanEqual), b) ->
        integer a && integer b
    | UnOp (Not, e) -> order e
    | _ -> false
  in
  if
    !Config.Verification.total && not !Config.under_approximation
    && Expr.Set.mem goal formulae
  then
    match goal with
    | Expr.UnOp
        (Not, BinOp
          ((UnOp (NumToInt,
              BinOp (BinOp ((LVar index as index_e), FPlus, Lit (Num 1.)),
                FMinus, Lit (Num 1.))) as predecessor_cast),
           Equal, (UnOp (NumToInt, LVar same_index) as index_cast)))
      when index = same_index && typed index Type.NumberType ->
        (* These are three exact original atoms, not a cancellation rewrite.
           Only the existing native UNSAT path may discharge their conjunction. *)
        let successor_cast = Expr.UnOp (NumToInt,
          Expr.BinOp (index_e, FPlus, Expr.num 1.)) in
        let core = Expr.Set.of_list
          [goal;
           Expr.BinOp (successor_cast, Equal,
             Expr.BinOp (Expr.int 1, IPlus, index_cast));
           Expr.BinOp (predecessor_cast, Equal,
             Expr.BinOp (Expr.int (-1), IPlus, successor_cast))] in
        if Expr.Set.cardinal core = 3 && Expr.Set.subset core formulae
           && not (Expr.Set.equal core formulae)
        then Some core else None
    | _ when order goal ->
        let core = Expr.Set.filter order formulae in
        let variables = Expr.lvars goal in
        let connected = Expr.Set.exists (fun premise ->
          not (Expr.equal premise goal)
          && not (SS.is_empty (SS.inter variables (Expr.lvars premise)))) core in
        (* Dropped Number facts can be the only useful premises for a cast.
           Decline an unrelated probe; the complete fallback retains them. *)
        if not connected || Expr.Set.equal core formulae then None else Some core
    | _ -> None
  else None

(* Replace only total, typed opaque Int leaves selected by integer_order_core.
   Every original model extends by assigning each fresh alias its term's value.
   The aliases have no added bounds/links; only native UNSAT can discharge the
   original conjunction. Unsupported integer-core terms keep the old path. *)
let integer_order_projection formulae core gamma =
  let rec integer = function
    | Expr.Lit (Int _) | LVar _
    | UnOp ((NumToInt | LstLen), LVar _) -> true
    | BinOp (a, (IPlus | IMinus), b) -> integer a && integer b
    | _ -> false
  in
  let rec order = function
    | Expr.BinOp (a, (Equal | ILessThan | ILessThanEqual), b) ->
        integer a && integer b
    | UnOp (Not, e) -> order e
    | _ -> false
  in
  if not (Expr.Set.for_all order core) then None
  else
    (* Match SMT's identifier encoding (# -> $$), including raw $$ names.
       Reserve the entire input namespace, not only the selected core. *)
    let encoded name = String.concat "$$" (String.split_on_char '#' name) in
    let names = Expr.Set.fold
      (fun e names -> SS.union names
        (SS.union (Expr.lvars e) (SS.union (Expr.pvars e) (Expr.locs e))))
      formulae SS.empty in
    let occupied = ref (Hashtbl.fold
      (fun name _ names -> SS.add (encoded name) names) gamma
      (SS.fold (fun name names -> SS.add (encoded name) names) names SS.empty)) in
    let next = ref 0 and aliases = ref Expr.Map.empty in
    let projected_gamma = Hashtbl.copy gamma in
    let rec fresh () =
      let name = "#integer_order_projection_" ^ string_of_int !next in
      incr next;
      if SS.mem (encoded name) !occupied then fresh ()
      else (
        occupied := SS.add (encoded name) !occupied;
        Hashtbl.add projected_gamma name Type.IntType;
        name)
    in
    let project e = Expr.map_opt (function
      | (Expr.UnOp ((NumToInt | LstLen), LVar _) as term) ->
          let name = match Expr.Map.find_opt term !aliases with
            | Some name -> name
            | None ->
                let name = fresh () in
                aliases := Expr.Map.add term name !aliases;
                name in
          Some (Expr.LVar name), false
      | e -> Some e, true) None e |> Option.get in
    let projected = Expr.Set.fold
      (fun e fs -> Expr.Set.add (project e) fs) core Expr.Set.empty in
    if Expr.Map.is_empty !aliases then None
    else Some (projected, projected_gamma, Expr.Map.bindings !aliases)

let integer_order_proved formulae core gamma =
  let projected_proved = match integer_order_projection formulae core gamma with
    | None -> false
    | Some (projected, projected_gamma, aliases) ->
        Smt.with_native_smt_context
          (fun () ->
            let expressions fs = `List
              (List.map Expr.to_yojson (Expr.Set.elements fs)) in
            `Assoc
              [ ("operation", `String "integer-order-projection");
                ("original_fs", expressions formulae);
                ("original_core", expressions core);
                ("projected_fs", expressions projected);
                ("aliases", `List (List.map (fun (term, name) ->
                  `Assoc [ ("term", Expr.to_yojson term);
                           ("alias", `String name) ]) aliases)) ])
          (fun () -> Smt.proves_unsat
            ~caller_kind:"optional-entailment-integer-order-projection"
            projected projected_gamma)
  in
  projected_proved || Smt.proves_unsat
    ~caller_kind:"optional-entailment-integer-order-core" core gamma

(* The captured prefix-step obligation needs its actual sequence length, not
   an opaque length alias. Select four existing atoms and replace only the two
   total Number-to-Int counts uniformly. Every original model extends to the
   fresh Int aliases, so only native UNSAT of this weaker query is sufficient.
   The original finite integral uint32 guards establish defined casts; they
   are eligibility checks, never projected premises or invented bounds. *)
let sequence_count_projection ~reserved_names ~original_gamma formulae gamma goal =
  let select values index count step =
    let typed name typ = Hashtbl.find_opt original_gamma name = Some typ
      && Hashtbl.find_opt gamma name = Some typ in
    let guards = Expr.Set.of_list
      [ Expr.UnOp (IsInt, index);
        Expr.BinOp (Expr.num 0., FLessThanEqual, index);
        Expr.BinOp (index, FLessThan, Expr.num 4294967295.) ] in
    let increment = Expr.BinOp (Expr.int 1, IPlus, count) in
    let core = Expr.Set.of_list
      [ goal; Expr.BinOp (Expr.int 0, ILessThanEqual, count);
        Expr.BinOp (step, Equal, increment);
        Expr.BinOp (increment, ILessThanEqual, Expr.UnOp (LstLen, values)) ] in
    match values,index with
    | Expr.LVar list_name, Expr.LVar index_name
      when typed list_name Type.ListType && typed index_name Type.NumberType
        && Expr.Set.subset guards formulae && Expr.Set.cardinal core = 4
        && Expr.Set.subset core formulae && not (Expr.Set.equal core formulae) ->
        let encoded name = String.concat "$$" (String.split_on_char '#' name) in
        let occupied = ref (SS.fold (fun name names ->
          SS.add (encoded name) names) (Lazy.force reserved_names) SS.empty) in
        Expr.Set.iter (fun e ->
          let names = SS.union (Expr.lvars e)
            (SS.union (Expr.pvars e) (Expr.locs e)) in
          SS.iter (fun name -> occupied := SS.add (encoded name) !occupied) names)
          formulae;
        Hashtbl.iter (fun name _ -> occupied := SS.add (encoded name) !occupied) gamma;
        let projected_gamma = Hashtbl.copy gamma in
        let next = ref 0 in
        let rec fresh () =
          let name = "#sequence_count_projection_" ^ string_of_int !next in
          incr next;
          if SS.mem (encoded name) !occupied then fresh ()
          else (
            occupied := SS.add (encoded name) !occupied;
            Hashtbl.add projected_gamma name Type.IntType;
            name)
        in
        let count_name = fresh () in
        let step_name = fresh () in
        let aliases = [count,count_name; step,step_name] in
        let project e = Expr.map_opt (fun e ->
          match List.find_opt (fun (term,_) -> Expr.equal term e) aliases with
          | Some (_,name) -> Some (Expr.LVar name),false
          | None -> Some e,true) None e |> Option.get in
        let projected = Expr.Set.fold (fun e fs -> Expr.Set.add (project e) fs)
          core Expr.Set.empty in
        Some (core,projected,projected_gamma,aliases)
    | _ -> None
  in
  if not !Config.Verification.total || !Config.under_approximation
     || not (Expr.Set.mem goal formulae) then None
  else match goal with
    | Expr.UnOp (Not, BinOp
        (LstSub ((LVar _ as values), Lit (Int zero),
           (UnOp (NumToInt, BinOp ((LVar _ as index), FPlus, Lit (Num one))) as step)),
         Equal, NOp (LstCat,
           [ LstSub (same, Lit (Int zero'), (UnOp (NumToInt, same_index) as count));
             EList [BinOp (same', LstNth, same_count)] ])))
      when Z.equal zero Z.zero && Z.equal zero' Z.zero && one = 1.
        && Expr.equal values same && Expr.equal values same'
        && Expr.equal index same_index && Expr.equal count same_count ->
        select values index count step
    | _ -> None

let sequence_count_proved ~reserved_names ~original_gamma formulae gamma goal =
  match sequence_count_projection ~reserved_names ~original_gamma formulae gamma goal with
  | None -> false
  | Some (core,projected,projected_gamma,aliases) ->
      Smt.with_native_smt_context
        (fun () ->
          let expressions fs = `List
            (List.map Expr.to_yojson (Expr.Set.elements fs)) in
          `Assoc
            [ ("operation", `String "sequence-count-projection");
              ("original_fs", expressions formulae);
              ("original_core", expressions core);
              ("projected_fs", expressions projected);
              ("aliases", `List (List.map (fun (term,name) ->
                `Assoc [("term",Expr.to_yojson term);("alias",`String name)]) aliases)) ])
        (fun () -> Smt.proves_unsat
          ~caller_kind:"optional-entailment-sequence-count-projection"
          projected projected_gamma)

(* The same finite counter domain supports machine-bound and nonnegative
   comparisons of both the original count and its exact +1 successor. Retain
   an original integer-literal comparison and three original range atoms;
   select the strict upper when present, otherwise the inclusive array bound.
   After all range/type gates, prefer original literal Int bounds on the exact
   same count, in the direction opposite the counterquery (including Not).
   No cast, comparison or bound is rewritten or inferred. The historical helper
   and caller names stay compatible; only native UNSAT proves any family case. *)
let successor_bound_core ~original_gamma formulae gamma goal =
  if not !Config.Verification.total || !Config.under_approximation
     || not (Expr.Set.mem goal formulae) then None
  else
    let count_index = function
      | Expr.UnOp (NumToInt, (LVar name as index)) -> Some (name,index)
      | UnOp (NumToInt, BinOp ((LVar name as index), FPlus, Lit (Num step)))
        when step = 1. -> Some (name,index)
      | _ -> None in
    let comparison = function
      | Expr.BinOp (Lit (Int _), (ILessThan | ILessThanEqual), count) ->
          Option.map (fun (name,index) -> (name,index,count,true)) (count_index count)
      | BinOp (count, (ILessThan | ILessThanEqual), Lit (Int _)) ->
          Option.map (fun (name,index) -> (name,index,count,false)) (count_index count)
      | _ -> None in
    let selected_index = match goal with
      | Expr.UnOp (Not, inner) ->
          Option.map (fun (name,index,count,upper) -> (name,index,count,not upper))
            (comparison inner)
      | _ -> comparison goal in
    match selected_index with
    | Some (name,index,count,prefer_upper)
      when Hashtbl.find_opt original_gamma name = Some Type.NumberType
        && Hashtbl.find_opt gamma name = Some Type.NumberType ->
        let upper = List.find_opt (fun e -> Expr.Set.mem e formulae)
          [ Expr.BinOp (index, FLessThan,Expr.num 4294967295.);
            Expr.BinOp (index, FLessThanEqual,Expr.num 4294967295.) ] in
        (match upper with
         | None -> None
         | Some upper ->
             let core = Expr.Set.of_list
               [goal;Expr.UnOp (IsInt,index);
                Expr.BinOp (Expr.num 0.,FLessThanEqual,index);upper] in
             if Expr.Set.cardinal core = 4 && Expr.Set.subset core formulae
                && not (Expr.Set.equal core formulae)
             then
               let bounds = Expr.Set.filter (fun atom ->
                 not (Expr.equal atom goal)
                 && match comparison atom with
                    | Some (_,_,same,upper) ->
                        Expr.equal same count && upper <> prefer_upper
                    | None -> false) formulae in
               let preferred = Expr.Set.add goal bounds in
               if not (Expr.Set.is_empty bounds)
                  && not (Expr.Set.equal preferred formulae)
               then Some preferred else Some core
             else None)
    | _ -> None

(* A finite-bound obligation on an original Number atom needs only its
   original positive IsInt certificate. Retain both exact existing atoms;
   native UNSAT is the proof, never a host arithmetic or domain assumption.
   The original caller types and positive premises must license the choice
   before any implication simplification can learn types or invent support. *)
let finite_number_bound_core
    ~matching ~existentials ~original_left_fs ~original_right_fs
    ~original_gamma formulae gamma goal =
  if not !Config.Verification.total || !Config.under_approximation
     || matching || not (SS.is_empty existentials)
     || not (Expr.Set.mem goal formulae)
  then None
  else
    match goal, original_right_fs with
    | Expr.UnOp (Not,wanted), [original] when Expr.equal wanted original ->
        finite_number_bound_pair
          ~original_fs:(Expr.Set.add goal (Lazy.force original_left_fs))
          ~original_gamma formulae gamma goal
    | _ -> None

(* Finite integral endpoints plus one original order fact suffice for these
   binary64 difference bounds. Submit only original atoms; native UNSAT of
   the weaker query proves the full conjunction. SAT/unknown keep fallback. *)
let finite_difference_core formulae gamma goal =
  let typed name = Hashtbl.find_opt gamma name = Some Type.NumberType in
  let endpoint = function
    | Expr.LVar name -> typed name
    | Lit (Num n) -> Float.is_finite n && Float.is_integer n
    | _ -> false
  in
  let select start finish order =
    (* A literal's finite integral domain is checked above. Do not invent an
       IsInt literal atom that normalisation removed from the original FS. *)
    let finish_facts = match finish with
      | Expr.Lit (Num _) -> []
      | _ -> [Expr.UnOp (IsInt, finish)]
    in
    let core = Expr.Set.of_list
      ([goal; Expr.UnOp (IsInt, start); order] @ finish_facts) in
    if Expr.Set.subset core formulae && not (Expr.Set.equal core formulae)
    then Some core else None
  in
  if not !Config.Verification.total || !Config.under_approximation
     || not (Expr.Set.mem goal formulae) then None
  else match goal with
  | Expr.UnOp (Not, BinOp
      (BinOp (BinOp ((LVar base as value), FPlus, Lit (Num 1.)),
         FMinus, Lit (Num 1.)), Equal, LVar same))
    when base = same && typed base ->
      (* Keep only four original atoms from the measured cancellation query.
         This is no rewrite: native UNSAT remains the sole sufficient result. *)
      let core = Expr.Set.of_list
        [goal; Expr.UnOp (IsInt, value);
         Expr.BinOp (Expr.num 0., FLessThanEqual, value);
         Expr.BinOp (value, FLessThanEqual, Expr.num 4294967295.)] in
      if Expr.Set.cardinal core = 4 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | Expr.UnOp
      (Not, BinOp (Lit (Num lower), FLessThanEqual,
        BinOp (finish_e, FMinus, (LVar start as start_e))))
    when lower = -. Float.max_float && typed start && endpoint finish_e ->
      (match select start_e finish_e (Expr.BinOp (start_e, FLessThanEqual, finish_e)) with
      | Some _ as core -> core
      | None -> select start_e finish_e (Expr.BinOp (start_e, FLessThan, finish_e)))
  | Expr.UnOp
      (Not, BinOp (Lit (Num lower), FLessThanEqual,
        BinOp (finish_e, FMinus,
          (BinOp (LVar start, FPlus, Lit (Num 1.)) as successor))))
    when lower = -. Float.max_float && typed start && endpoint finish_e ->
      (* Use the original successor finiteness and order premises. This
         lower-bound core adds no integer alias or successor identity; native
         UNSAT remains required, and every inconclusive result keeps fallback. *)
      select successor finish_e
        (Expr.BinOp (successor, FLessThanEqual, finish_e))
  | Expr.UnOp
      (Not, BinOp (BinOp (finish_e, FMinus,
        (LVar start as start_e)), FLessThanEqual, Lit (Num upper)))
    when upper = Float.max_float && typed start && endpoint finish_e ->
      select start_e finish_e (Expr.BinOp (Expr.num 0., FLessThanEqual, start_e))
  | Expr.UnOp
      (Not, BinOp (BinOp (finish_e, FMinus,
        (BinOp (LVar start, FPlus, Lit (Num 1.)) as successor)),
        FLessThanEqual, Lit (Num upper)))
    when upper = Float.max_float && typed start && endpoint finish_e ->
      (* Original start nonnegativity also bounds its rounded successor below.
         Require original successor/finish finiteness and real native UNSAT;
         no derived identity or upper-finiteness assumption is inserted. *)
      select successor finish_e
        (Expr.BinOp (Expr.num 0., FLessThanEqual, Expr.LVar start))
  | Expr.UnOp
      (Not, BinOp (BinOp
        ((BinOp (LVar base, FPlus, Lit (Num 1.)) as successor),
         FMinus, Lit (Num 1.)), FLessThanEqual, Lit (Num upper)))
    when upper = Float.max_float && typed base ->
      (* The original bounded integral successor suffices for this exact
         predecessor's finite upper bound. Add no identity or domain fact:
         only native UNSAT of this proper original subset can discharge it. *)
      let core = Expr.Set.of_list
        [goal; Expr.UnOp (IsInt, successor);
         Expr.BinOp (Expr.num 0., FLessThanEqual, successor);
         Expr.BinOp (successor, FLessThanEqual, Expr.num 4294967295.)] in
      if Expr.Set.subset core formulae && not (Expr.Set.equal core formulae)
      then Some core else None
  | _ -> None

(* A successor-order obligation can be discharged by its original order
   premise. This is only a weaker native binary64 query, not an arithmetic
   axiom: real UNSAT is required and SAT/unknown preserve every fallback. *)
let successor_order_core formulae gamma goal =
  let typed name = Hashtbl.find_opt gamma name = Some Type.NumberType in
  if not !Config.Verification.total || !Config.under_approximation
     || not (Expr.Set.mem goal formulae) then None
  else match goal with
  | Expr.UnOp
      (Not, BinOp ((LVar position as position_e), FLessThan,
        BinOp ((LVar start as start_e), FPlus, Lit (Num 1.))))
    when typed position && typed start ->
      let core = Expr.Set.of_list
        [goal; Expr.BinOp (Expr.num 0., FLessThanEqual, start_e);
         Expr.BinOp (start_e, FLessThanEqual, Expr.num 4294967294.);
         Expr.BinOp (position_e, Equal, start_e)] in
      if Expr.Set.cardinal core = 4 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | Expr.UnOp
      (Not, BinOp ((LVar position as position_e), FLessThanEqual,
        BinOp ((LVar start as start_e), FPlus, Lit (Num 1.))))
    when typed position && typed start ->
      let core = Expr.Set.of_list
        [goal; Expr.BinOp (position_e, FLessThanEqual, start_e)] in
      if Expr.Set.cardinal core = 2 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | Expr.UnOp
      (Not, BinOp (BinOp ((LVar position as position_e), FPlus, Lit (Num 1.)),
        FLessThanEqual, BinOp ((LVar start as start_e), FPlus, Lit (Num 1.))))
    when typed position && typed start ->
      let core = Expr.Set.of_list
        [goal; Expr.BinOp (position_e, FLessThanEqual, start_e);
         Expr.UnOp (IsInt, position_e); Expr.UnOp (IsInt, start_e);
         Expr.BinOp (Expr.num 0., FLessThanEqual, position_e);
         Expr.BinOp (Expr.num 0., FLessThanEqual, start_e);
         Expr.BinOp (position_e, FLessThanEqual, Expr.num 4294967294.);
         Expr.BinOp (start_e, FLessThanEqual, Expr.num 4294967294.)] in
      if Expr.Set.cardinal core = 8 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | Expr.UnOp
      (Not, BinOp (BinOp ((LVar index as index_e), FPlus, Lit (Num 1.)),
        FLessThanEqual, (LVar limit as limit_e)))
    when typed index && typed limit ->
      (* Exact original integral UInt32 endpoints and strict order. No fact or
         cast is added: only native UNSAT of this proper subset licenses it. *)
      let core = Expr.Set.of_list
        [goal; Expr.UnOp (IsInt, index_e); Expr.UnOp (IsInt, limit_e);
         Expr.BinOp (Expr.num 0., FLessThanEqual, index_e);
         Expr.BinOp (Expr.num 0., FLessThanEqual, limit_e);
         Expr.BinOp (index_e, FLessThanEqual, Expr.num 4294967295.);
         Expr.BinOp (limit_e, FLessThanEqual, Expr.num 4294967295.);
         Expr.BinOp (index_e, FLessThan, limit_e)] in
      if Expr.Set.cardinal core = 8 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | Expr.UnOp
      (Not, BinOp (BinOp ((LVar position as position_e), FPlus, Lit (Num 1.)),
        FLessThanEqual, Lit (Num upper)))
    when typed position && Float.is_finite upper
         && 1. <= upper && upper <= 9007199254740992.
         && Float.floor upper = upper && (upper -. 1.) +. 1. = upper ->
      let core = Expr.Set.of_list
        [goal; Expr.BinOp (Expr.num 0., FLessThanEqual, position_e);
         Expr.BinOp (position_e, FLessThanEqual, Expr.num (upper -. 1.))] in
      if Expr.Set.cardinal core = 3 && Expr.Set.subset core formulae
         && not (Expr.Set.equal core formulae)
      then Some core else None
  | _ -> None


(* Pure original-fact proof, before mixed-list simplification. Ordinary Number
   equality is used only under the SAME finite nonzero rounded addition; the
   generic native congruence control certifies exact equality of those sums.
   No Number variable is substituted, and no premise/type/state is changed. *)
let original_successor_alias_facts_prove
    ~matching existentials left_fs right_fs gamma =
  if not !Config.Verification.total || !Config.under_approximation
     || matching || not (SS.is_empty existentials) || right_fs = []
     || PFS.mem left_fs Expr.false_
  then false
  else
    let facts = PFS.to_list left_fs in
    let typed name typ = Type_env.get gamma name = Some typ in
    let bits_equal a b = Int64.equal (Int64.bits_of_float a) (Int64.bits_of_float b) in
    let rec number = function
      | Expr.LVar name -> typed name Type.NumberType
      | Lit (Num n) -> Float.is_finite n
      | BinOp (a, (FPlus | FMinus), b) -> number a && number b
      | _ -> false
    in
    let rec integer = function
      | Expr.LVar name -> typed name Type.IntType
      | Lit (Int _) -> true
      | UnOp (NumToInt, n) -> number n
      | BinOp (a, (IPlus | IMinus), b) -> integer a && integer b
      | _ -> false
    in
    let int_aliases name =
      List.filter_map
        (function
          | Expr.BinOp (a, Equal, b) ->
              let candidate = match a, b with
                | LVar v, rhs when String.equal v name -> Some rhs
                | lhs, LVar v when String.equal v name -> Some lhs
                | _ -> None
              in
              (match candidate with
              | Some (LVar v) when String.equal v name -> None
              | Some rhs when integer rhs -> Some rhs
              | _ -> None)
          | _ -> None)
        facts
    in
    let rec resolve seen = function
      | Expr.LVar name as e when typed name Type.IntType ->
          if SS.mem name seen then None
          else (match int_aliases name with
            | [] -> Some e
            | [rhs] -> resolve (SS.add name seen) rhs
            | _ -> None)
      | Lit (Int _) as e -> Some e
      | UnOp (NumToInt, n) as e when number n -> Some e
      | BinOp (a, ((IPlus | IMinus) as op), b) ->
          (match resolve seen a, resolve seen b with
          | Some a, Some b -> Some (Expr.BinOp (a, op, b))
          | _ -> None)
      | _ -> None
    in
    let combine left right = match left, right with
      | Some a, Some b -> Some (a || b)
      | _ -> None
    in
    let rec same_number a (b : Expr.t) = match a, b with
      | Expr.LVar x, LVar y when String.equal x y && typed x Type.NumberType ->
          Some false
      | Lit (Num x), Lit (Num y)
        when Float.is_finite x && Float.is_finite y && bits_equal x y ->
          Some false
      | BinOp (LVar x, FPlus, Lit (Num k)),
        BinOp (LVar y, FPlus, Lit (Num l))
        when not (String.equal x y) && typed x Type.NumberType
             && typed y Type.NumberType && Float.is_finite k
             && k <> 0. && bits_equal k l
             && (PFS.mem left_fs (Expr.BinOp (LVar x, Equal, LVar y))
                 || PFS.mem left_fs (Expr.BinOp (LVar y, Equal, LVar x))) ->
          Some true
      | BinOp (a, ((FPlus | FMinus) as op), b),
        BinOp (c, other, d) when op = other ->
          combine (same_number a c) (same_number b d)
      | _ -> None
    in
    let rec same_integer a (b : Expr.t) = match a, b with
      | Expr.LVar x, LVar y when String.equal x y && typed x Type.IntType ->
          Some false
      | Lit (Int x), Lit (Int y) when Z.equal x y -> Some false
      | UnOp (NumToInt, x), UnOp (NumToInt, y) -> same_number x y
      | BinOp (a, ((IPlus | IMinus) as op), b),
        BinOp (c, other, d) when op = other ->
          combine (same_integer a c) (same_integer b d)
      | _ -> None
    in
    let terms a b = match resolve SS.empty a, resolve SS.empty b with
      | Some a, Some b -> same_integer a b
      | _ -> None
    in
    let proves goal (fact : Expr.t) = match goal, fact with
      | Expr.BinOp (a, ((ILessThan | ILessThanEqual) as op), b),
        BinOp (c, other, d) when op = other ->
          combine (terms a c) (terms b d)
      | _ -> None
    in
    let proof goal = match List.filter_map (proves goal) facts with
      | [used_successor_alias] -> Some used_successor_alias
      | _ -> None
    in
    match List.fold_left
      (fun result goal -> combine result (proof goal))
      (Some false) right_fs with
    | Some true -> true
    | _ -> false

(* Use only the original positive implication premises and input types. The
   caller invokes this pure map before simplification can learn types or merge
   the negated goal into a consistency query. IsInt certifies a finite Number;
   its retained nonnegative value has a nonnegative exact integer conversion.
   Original expression-domain checks remain the state checker's obligation. *)
let reduce_original_nonnegative_cast_goals
    ~matching existentials left_fs gamma right_fs =
  if not !Config.Verification.total || !Config.under_approximation
     || matching || not (SS.is_empty existentials)
  then right_fs
  else
    let rec total_number (e : Expr.t) =
      match e with
      | LVar name | PVar name ->
          Type_env.get gamma name = Some Type.NumberType
      | Lit (Num number) -> Float.is_finite number
      | BinOp (left, (FPlus | FMinus), right) ->
          total_number left && total_number right
      | UnOp (ToIntOp, operand) -> total_number operand
      | _ -> false
    in
    List.map
      (fun (goal : Expr.t) ->
        match goal with
        | BinOp (Lit (Int zero), ILessThanEqual, UnOp (NumToInt, operand))
          when Z.equal zero Z.zero && total_number operand
               && PFS.mem left_fs (UnOp (IsInt, operand))
               && PFS.mem left_fs
                    (BinOp (Lit (Num 0.), FLessThanEqual, operand)) ->
            Expr.Lit (Bool true)
        | _ -> goal)
      right_fs

let check_entailment_simplified
    ?(matching = false)
    (existentials : SS.t)
    (left_fs : PFS.t)
    (right_fs : Expr.t list)
    (gamma : Type_env.t) : bool =
  (* The optional typed-alias core may only retain literal caller atoms and
     an originally declared witness type, never a type inferred from its link. *)
  let finite_bound_original_existentials = existentials in
  let typed_alias_original_right_fs = right_fs in
  let typed_alias_original_left_fs =
    lazy (Expr.Set.of_list (PFS.to_list left_fs))
  in
  (* Reserve the unsimplified caller namespace lazily. An unused Gamma name or
     a fact later eliminated by simplification must not collide with a fresh
     projected alias. None of these caller structures is mutated. *)
  let sequence_projection_original_gamma = Type_env.as_hashtbl gamma in
  let sequence_projection_reserved = lazy (
    let names = List.fold_left (fun names e ->
      SS.union names (SS.union (Expr.lvars e)
        (SS.union (Expr.pvars e) (Expr.locs e))))
      SS.empty (right_fs @ PFS.to_list left_fs) in
    Hashtbl.fold (fun name _ names -> SS.add name names)
      (Type_env.as_hashtbl gamma) names) in
  L.verbose (fun m ->
      m
        "Preparing entailment check:@\n\
         Existentials:@\n\
         @[<h>%a@]@\n\
         Left:%a@\n\
         Right:%a@\n\
         Gamma:@\n\
         %a@\n"
        (Fmt.iter ~sep:Fmt.comma SS.iter Fmt.string)
        existentials PFS.pp left_fs PFS.pp (PFS.of_list right_fs) Type_env.pp
        gamma);

  (* SOUNDNESS !!DANGER!!: call to simplify_implication       *)
  (* Simplify maximally the implication to be checked         *)
  (* Remove from the typing environment the unused variables  *)
  (* let t = Unix.gettimeofday () in *)
  let left_fs = PFS.copy left_fs in
  let gamma = Type_env.copy gamma in
  let right_fs =
    reduce_original_nonnegative_cast_goals ~matching existentials left_fs gamma
      right_fs
  in
  let right_fs = PFS.of_list right_fs in
  let left_lvars = PFS.lvars left_fs in
  let right_lvars = PFS.lvars right_fs in
  let existentials =
    Simplifications.simplify_implication ~matching existentials left_fs right_fs
      gamma
  in
  Type_env.filter_vars_in_place gamma (SS.union left_lvars right_lvars);

  (* Separate gamma into existentials and non-existentials *)
  let left_fs = PFS.to_list left_fs in
  let right_fs = PFS.to_list right_fs in
  let gamma_left =
    Type_env.filter gamma (fun v -> not (SS.mem v existentials))
  in
  let gamma_right = Type_env.filter gamma (fun v -> SS.mem v existentials) in

  (* If left side is false, return false *)
  if List.mem Expr.false_ (left_fs @ right_fs) then false
  else
    (* Check satisfiability of left side *)
    let left_sat =
      true
      (* Smt.check_sat (Formula.Set.of_list left_fs) gamma_left *)
    in

    (* assert (left_sat = true); *)

    (* If the right side is empty or left side is not satisfiable, return the result of
       checking left-side satisfiability *)
    if List.length right_fs = 0 || not left_sat then left_sat
    else
      (* A => B -> Axioms(A) /\ Axioms(B) /\ A => B
                -> !(Axioms(A) /\ Axioms(B) /\ A) \/ B
                -> Axioms(A) /\ Axioms(B) /\ A /\ !B is SAT *)
      (* Existentials in B need to be turned into universals *)
      (* A => Exists (x1, ..., xn) B
                -> Axioms(A) /\ A => (Exists (x1, ..., xn) (Axioms(B) => B)
                -> !(Axioms(A) /\ A) \/ (Exists (x1, ..., xn) (Axioms(B) => B))
                -> Axioms(A) /\ A /\ (ForAll (x1, ..., x2) Axioms(B) /\ !B) is SAT
                -> ForAll (x1, ..., x2)  Axioms(A) /\ Axioms(B) /\ A /\ !B is SAT *)

      (* Get axioms *)
      (* let axioms   = get_axioms (left_fs @ right_fs) gamma in *)
      let right_fs = List.map Expr.negate right_fs in
      let right_f : Expr.t =
        if SS.is_empty existentials then Expr.disjunct right_fs
        else
          let binders =
            List.map
              (fun x -> (x, Type_env.get gamma_right x))
              (SS.elements existentials)
          in
          ForAll (binders, Expr.disjunct right_fs)
      in

      let formulae = PFS.of_list (right_f :: (left_fs @ [] (* axioms *))) in
      let goal_subst, _ =
        Simplifications.simplify_pfs_and_gamma formulae gamma_left
      in
      (* Shortcut selectors must use the goal in the simplified conjunction.
         This only updates selection metadata: every sufficient query still
         consists of retained facts and requires native UNSAT; the complete
         fallback below is unchanged. *)
      let right_f =
        SESubst.subst_in_expr goal_subst ~partial:true right_f
        |> Reduction.reduce_lexpr ~matching ~gamma:gamma_left
      in
      let formulae = Expr.Set.of_list (PFS.to_list formulae) in
      let focused =
        if !Config.Verification.total && SS.is_empty existentials then
          let relevant e =
            let overlap vars =
              let goal = vars right_f and current = vars e in
              not (SS.is_empty (SS.inter goal current))
            in
            let ground =
              SS.is_empty (Expr.lvars e)
              && SS.is_empty (Expr.pvars e)
              && SS.is_empty (Expr.locs e)
            in
            ground || overlap Expr.lvars || overlap Expr.pvars
            || overlap Expr.locs
          in
          Expr.Set.filter relevant formulae
        else formulae
      in
      (* Removing assumptions weakens the conjunction. Only its UNSAT result
         proves the full query; SAT/unknown must use the complete query below.
         Never use this sufficient check for branch feasibility. *)
      (* Omitting only untyped structural bookkeeping rarely helps search.
         Require an omitted fact with a known logical-variable type before
         paying for the optional query. This changes eligibility, not logic. *)
      let gamma_tbl = Type_env.as_hashtbl gamma in
      let useful_omission =
        Expr.Set.exists
          (fun e -> SS.exists (Hashtbl.mem gamma_tbl) (Expr.lvars e))
          (Expr.Set.diff formulae focused)
      in
      let observes_number_to_utf16 e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super

            method! visit_expr () e =
              (match e with
              | Expr.UnOp (NumberToUtf16, _) -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      let observes_contents e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super

            method! visit_expr () e =
              (match e with
              | BinOp (_, (Utf16Nth | Utf16CodeUnit), _) -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      (* A contained-variable subset observing UTF-16 length may omit the
         numeric alias that establishes an index bound. Exclude both direct
         integer lengths and nested rounded forms from this optional path;
         retain the richer focused and complete fallback queries below. *)
      let observes_utf16_length e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super

            method! visit_expr () e =
              (match e with
              | Expr.UnOp (Utf16Len, _) -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      (* A mixed List-length/Number cast goal keeps the richer/full query;
         dropping typed premises is only an optional sufficient optimization. *)
      let observes_list_length e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super

            method! visit_expr () e =
              (match e with
              | Expr.UnOp (LstLen, _) -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      (* Uint32 goals may retain costly formatter facts while a weakened
         conjunction is satisfiable. Skip these optional sufficient probes;
         the complete counterquery below still decides every such goal. *)
      let observes_uint32 ?(operand = fun _ -> true) e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super
            method! visit_expr () e =
              (match e with
              | Expr.UnOp (ToUint32Op, e) when operand e -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      (* Plain count goals can retain the same Uint32 formatter constraints.
         Require a goal variable with the original integral native-count bound;
         unrelated UTF16/index conversions retain their sufficient proof path. *)
      let count_variable name =
        let n = Expr.LVar name in
        Hashtbl.find_opt gamma_tbl name = Some Type.NumberType
        && SS.mem name (Expr.lvars right_f)
        && Expr.Set.mem (Expr.UnOp (IsInt, n)) formulae
        && Expr.Set.mem (Expr.BinOp (Expr.num 0., FLessThanEqual, n)) formulae
        && Expr.Set.mem (Expr.BinOp (n, FLessThan, Expr.num 4294967295.)) formulae
      in
      let rec count_operand = function
        | Expr.LVar name -> count_variable name
        | Expr.BinOp (e, (FPlus | FMinus), Lit (Num _))
        | Expr.BinOp (Lit (Num _), FPlus, e) -> count_operand e
        | _ -> false
      in
      let uint32_query =
        observes_uint32 right_f
        || Expr.Set.exists (observes_uint32 ~operand:count_operand) formulae
      in
      let contained =
        if
          !Config.Verification.total && SS.is_empty existentials
          && not (observes_contents right_f)
        then
          (* Keep direct, already-typed aliases of the exact indexed values
             queried by TypeOf. These names only widen relevance: every
             retained formula is still an original conjunct, and only native
             UNSAT of the sufficient subset can close the entailment. *)
          let lookups = ref Expr.Set.empty in
          let visitor =
            object
              inherit [_] Visitors.iter as super
              method! visit_expr () e =
                (match e with
                | Expr.UnOp (TypeOf, (BinOp (_, LstNth, _) as lookup)) ->
                    lookups := Expr.Set.add lookup !lookups
                | _ -> ());
                super#visit_expr () e
            end
          in
          visitor#visit_expr () right_f;
          let relevant_lvars =
            Expr.Set.fold
              (fun e names ->
                match e with
                | Expr.BinOp (LVar name, Equal, lookup)
                  when Hashtbl.mem gamma_tbl name
                       && Expr.Set.mem lookup !lookups ->
                    SS.add name names
                | Expr.BinOp (lookup, Equal, LVar name)
                  when Hashtbl.mem gamma_tbl name
                       && Expr.Set.mem lookup !lookups ->
                    SS.add name names
                | _ -> names)
              formulae (Expr.lvars right_f)
          in
          Expr.Set.filter
            (fun e ->
              (not (observes_contents e))
              && SS.subset (Expr.lvars e) relevant_lvars
              && SS.subset (Expr.pvars e) (Expr.pvars right_f)
              && SS.subset (Expr.locs e) (Expr.locs right_f))
            formulae
        else formulae
      in
      (* Only narrow the operand of the existing contained native check.
         Keep [contained] itself for every old eligibility/fallback comparison.
         The exact lookup occurs in both unchanged atoms, so no index/key
         identity, bound, type assertion or other premise is synthesized. *)
      let typed_alias_contained =
        if !Config.Verification.total && SS.is_empty existentials then
          match (right_f, typed_alias_original_right_fs) with
          | Expr.UnOp
              (Not,
               Expr.BinOp
                 (Expr.UnOp (TypeOf, (Expr.BinOp (_, LstNth, _) as lookup)),
                  Equal, Expr.Lit (Literal.Type Type.Utf16Type))),
            [original_goal]
            when Expr.equal right_f (Expr.negate original_goal)
                 && Expr.Set.mem right_f formulae ->
              let original_left = Lazy.force typed_alias_original_left_fs in
              let exact_witness = function
                | Expr.BinOp (LVar name, Equal, other)
                  when Expr.equal other lookup -> Some name
                | Expr.BinOp (other, Equal, LVar name)
                  when Expr.equal other lookup -> Some name
                | _ -> None
              in
              let aliases =
                Expr.Set.filter
                  (fun atom ->
                    Expr.Set.mem atom original_left
                    && (match exact_witness atom with
                        | Some name ->
                            Hashtbl.find_opt sequence_projection_original_gamma name
                              = Some Type.Utf16Type
                            && Hashtbl.find_opt gamma_tbl name
                                 = Some Type.Utf16Type
                        | None -> false))
                  formulae
              in
              (match Expr.Set.elements aliases with
              | [alias] ->
                  let core = Expr.Set.of_list [right_f; alias] in
                  if Expr.Set.cardinal core = 2
                     && Expr.Set.subset core formulae
                     && not (Expr.Set.equal core formulae)
                  then Some core
                  else None
              | _ -> None)
          | _ -> None
        else None
      in
      let contained_omission =
        Expr.Set.exists
          (fun e -> SS.exists (Hashtbl.mem gamma_tbl) (Expr.lvars e))
          (Expr.Set.diff formulae contained)
      in
      let number_variables e =
        SS.is_empty (Expr.pvars e)
        && SS.is_empty (Expr.locs e)
        && SS.for_all
             (fun name ->
               Hashtbl.find_opt gamma_tbl name = Some Type.NumberType)
             (Expr.lvars e)
      in
      (* Numeric goal weakenings retaining Number-to-integer casts can
         lose the premises needed by mixed FP/BV/Int arithmetic. Keep the
         complete query for this shape; do not change its formulas or policy. *)
      let observes_number_cast e =
        let found = ref false in
        let visitor =
          object
            inherit [_] Visitors.iter as super
            method! visit_expr () e =
              (match e with
              | Expr.UnOp (NumToInt, _) -> found := true
              | _ -> ());
              super#visit_expr () e
          end
        in
        visitor#visit_expr () e;
        !found
      in
      let numeric_cast_query =
        !Config.Verification.total && SS.is_empty existentials
        && number_variables right_f
        && Expr.Set.exists observes_number_cast formulae
      in
      let numeric =
        if
          !Config.Verification.total && SS.is_empty existentials
          && (not (SS.is_empty (Expr.lvars right_f)))
          && number_variables right_f
        then Expr.Set.filter number_variables formulae
        else formulae
      in
      (* Keep numeric dependencies omitted by the contained-variable attempt,
         while dropping string/heap links from a purely numeric goal. These
         are still original facts: only native UNSAT licenses success. *)
      let numeric_omission =
        (not (Expr.Set.equal numeric formulae))
        && not (Expr.Set.equal numeric contained)
      in
      (* A conjunction of numeric goals becomes a disjunction of failures.
         Prove each failure impossible separately, using the same original
         numeric premises. All pieces must be UNSAT. This is only sufficient;
         any SAT/unknown keeps the combined and complete fallbacks below.
         The numeric subset is enabled only without shared existentials. *)
      let numeric_pieces_proved () =
        let rec disjuncts = function
          | Expr.BinOp (left, Or, right) -> disjuncts left @ disjuncts right
          | e -> [ e ]
        in
        let pieces = disjuncts right_f in
        List.length pieces > 1
        && Expr.Set.mem right_f numeric
        && List.for_all
             (fun piece ->
               Smt.proves_unsat ~caller_kind:"optional-entailment-numeric-piece"
                 (Expr.Set.add piece (Expr.Set.remove right_f numeric))
                 gamma_tbl)
             pieces
      in
      (* Empty UTF-16 length sufficient check. The negated goal
         Not((u16-len s) == 0), one original numeric link n == as_num(u16-len s),
         the original zero equation n == 0., and one original integer upper bound
         (u16-len s) <= b are all original conjuncts of the full query. Dropping
         the other conjuncts weakens the query, so native UNSAT on this
         four-expression subset suffices; SAT or unknown fall back below. *)
      let length_zero_proved () =
        let enabled =
          !Config.Verification.total
          && (not !Config.under_approximation)
          && SS.is_empty existentials
          && Expr.Set.mem right_f formulae
        in
        if not enabled then false
        else
          match right_f with
          | Expr.UnOp
              ( Not,
                Expr.BinOp
                  ( Expr.UnOp (Utf16Len, Expr.LVar s),
                    Equal,
                    Expr.Lit (Int goal_zero) ) )
            when Z.equal goal_zero Z.zero
                 && Hashtbl.find_opt gamma_tbl s = Some Type.Utf16Type -> (
              let link_of e =
                match e with
                | Expr.BinOp
                    ( Expr.LVar n,
                      Equal,
                      Expr.UnOp (IntToNum, Expr.UnOp (Utf16Len, Expr.LVar s2))
                    )
                  when s2 = s
                       && Hashtbl.find_opt gamma_tbl n = Some Type.NumberType ->
                    Some (n, e)
                | _ -> None
              in
              let bound_of e =
                match e with
                | Expr.BinOp
                    ( Expr.UnOp (Utf16Len, Expr.LVar s2),
                      ILessThanEqual,
                      Expr.Lit (Int _) )
                  when s2 = s -> Some e
                | _ -> None
              in
              (* Deterministic (Set) order; at most one native attempt. *)
              let links =
                Expr.Set.fold
                  (fun e acc ->
                    match link_of e with
                    | Some t -> t :: acc
                    | None -> acc)
                  formulae []
              in
              match
                List.find_map
                  (fun (n, link_e) ->
                    let zero_e =
                      Expr.BinOp (Expr.LVar n, Equal, Expr.Lit (Num 0.))
                    in
                    if not (Expr.Set.mem zero_e formulae) then None
                    else
                      List.find_map bound_of (Expr.Set.elements formulae)
                      |> Option.map (fun bound_e -> (link_e, zero_e, bound_e)))
                  links
              with
              | Some (link_e, zero_e, bound_e) ->
                  let core =
                    Expr.Set.of_list [ right_f; link_e; zero_e; bound_e ]
                  in
                  Expr.Set.cardinal core = 4
                  && Expr.Set.subset core formulae
                  && (not (Expr.Set.equal core formulae))
                  && Smt.proves_unsat ~caller_kind:"optional-entailment-length-zero" core gamma_tbl
              | None -> false)
          | _ -> false
      in
      (* Keep only two original same-access order facts. Native UNSAT of this
         weaker query suffices; SAT/unknown keeps every existing fallback. No
         UTF-16 range fact or arithmetic identity is assumed or added. *)
      let utf16_code_order_proved () =
        let enabled =
          !Config.Verification.total
          && (not !Config.under_approximation)
          && SS.is_empty existentials
          && Expr.Set.mem right_f formulae
        in
        if not enabled then false
        else
          match right_f with
          | Expr.UnOp
              ( Not,
                Expr.BinOp
                  ( (Expr.Lit (Num _) as bound),
                    FLessThanEqual,
                    (Expr.BinOp (_, Utf16CodeUnit, _) as code) ) ) ->
              let premise =
                Expr.UnOp (Not, Expr.BinOp (code, FLessThan, bound))
              in
              let core = Expr.Set.of_list [ right_f; premise ] in
              Expr.Set.cardinal core = 2
              && Expr.Set.subset core formulae
              && (not (Expr.Set.equal core formulae))
              && Smt.proves_unsat ~caller_kind:"optional-entailment-code-order" core gamma_tbl
          | _ -> false
      in
      (* This weaker arithmetic query can prove the complete conjunction only
         by native UNSAT. SAT/unknown retain the original focused/full paths. *)
      (* Optional-shortcut eligibility: a subset observing UTF-16 contents or
         a rounded length alias may drop the alias that witnesses UNSAT, so its
         optional query is skipped and the complete fallback below is kept. *)
      let model =
        if
          SS.is_empty existentials
          && (match finite_number_bound_core ~matching
             ~existentials:finite_bound_original_existentials
             ~original_left_fs:typed_alias_original_left_fs
             ~original_right_fs:typed_alias_original_right_fs
             ~original_gamma:sequence_projection_original_gamma
             formulae gamma_tbl right_f with
           | None -> false
           | Some core -> Smt.with_native_smt_context
               (fun () ->
                 let expressions fs = `List
                   (List.map Expr.to_yojson (Expr.Set.elements fs)) in
                 `Assoc
                   [ ("operation", `String "finite-number-bound-core");
                     ("original_fs", expressions formulae);
                     ("original_core", expressions core);
                     ("query_gamma", `String (Fmt.str "%a" Type_env.pp gamma));
                     ("query_gamma_bindings", `List
                       (Hashtbl.fold (fun name typ rows ->
                          `List [`String name; `String (Type.str typ)] :: rows)
                          gamma_tbl [] |> List.sort Stdlib.compare)) ])
               (fun () -> Smt.proves_unsat
                 ~caller_kind:"optional-entailment-finite-number-bound-core"
                 core gamma_tbl))
        then None
        else if
          SS.is_empty existentials
          && sequence_count_proved ~reserved_names:sequence_projection_reserved
               ~original_gamma:sequence_projection_original_gamma
               formulae gamma_tbl right_f
        then None
        else if
          SS.is_empty existentials
          && (match successor_bound_core
                ~original_gamma:sequence_projection_original_gamma
                formulae gamma_tbl right_f with
              | None -> false
              | Some core -> Smt.with_native_smt_context
                  (fun () ->
                    let expressions fs = `List
                      (List.map Expr.to_yojson (Expr.Set.elements fs)) in
                    `Assoc
                      [ ("operation", `String "numeric-successor-bound-core");
                        ("original_fs", expressions formulae);
                        ("original_core", expressions core) ])
                  (fun () -> Smt.proves_unsat
                    ~caller_kind:"optional-entailment-numeric-successor-bound-core"
                    core gamma_tbl))
        then None
        else if
          SS.is_empty existentials
          && (match integer_order_core formulae gamma_tbl right_f with
             | Some core -> integer_order_proved formulae core gamma_tbl
             | None -> false)
        then None
        else if
          SS.is_empty existentials
          && (match finite_difference_core formulae gamma_tbl right_f with
             | Some core -> Smt.proves_unsat ~caller_kind:"optional-entailment-finite-difference-core" core gamma_tbl
             | None -> false)
        then None
        else if SS.is_empty existentials &&
          (match successor_order_core formulae gamma_tbl right_f with
          | Some core -> Smt.proves_unsat ~caller_kind:"optional-entailment-successor-order-core" core gamma_tbl
          | None -> false)
        then None
        else if length_zero_proved () then None
        else if utf16_code_order_proved () then None
        else if
          contained_omission
          (* Pure-Number goals need their numeric bridge premises. Keep the
             richer numeric path and complete fallback, not this weakening. *)
          && not (number_variables right_f)
          && not uint32_query
          && (not (Expr.Set.exists observes_utf16_length contained))
          && not (observes_list_length right_f && observes_number_cast right_f)
          && Smt.proves_unsat ~caller_kind:"optional-entailment-contained"
               (Option.value ~default:contained typed_alias_contained) gamma_tbl
        then None
        else if
          numeric_omission
          && not numeric_cast_query
          && not uint32_query
          && (numeric_pieces_proved () || Smt.proves_unsat ~caller_kind:"optional-entailment-numeric" numeric gamma_tbl)
        then None
        else if
          useful_omission
          && not numeric_cast_query
          && not uint32_query
          (* A pure-Number query already has the complete numeric path. A
             focused subset can discard its transitive integrality/bounds. *)
          && (not (Expr.Set.for_all number_variables formulae))
          && (not (Expr.Set.exists observes_contents focused))
          (* Length/index goals can omit numeric facts connected through an
             alias, even when the focused query retains the string itself.
             Use the complete query rather than this optional weakening. *)
          && (not (Expr.Set.exists observes_utf16_length focused))
          (* Formatter-bearing focused subsets can retain costly UTF16 facts
             while omitting typed bounds. Keep the complete fallback. *)
          && (not (Expr.Set.exists observes_number_to_utf16 focused))
          && Smt.proves_unsat ~caller_kind:"optional-entailment-focused" focused gamma_tbl
        then None
        else Smt.check_sat formulae (Type_env.as_hashtbl gamma)
      in
      let ret = Option.is_none model in
      L.(verbose (fun m -> m "Entailment returned %b" ret));
      let () =
        model
        |> Option.iter (fun model ->
               L.tmi (fun m -> m "Here's the model:\n%a" Smt.pp_model model))
      in
      (* Utils.Statistics.update_statistics "FOS: CheckEntailment"
         (Unix.gettimeofday () -. t); *)
      ret

let check_entailment ?(matching = false) existentials left_fs right_fs gamma =
  Smt.with_native_smt_context
    (fun () ->
      `Assoc
          [ ("operation", `String "entailment");
            ("matching", `Bool matching);
            ("original_existentials", `List (List.map (fun x -> `String x) (SS.elements existentials)));
            ("original_left_fs", `List (List.map (fun e -> `String (Fmt.str "%a" Expr.pp e)) (PFS.to_list left_fs)));
            ("original_right_fs", `List (List.map (fun e -> `String (Fmt.str "%a" Expr.pp e)) right_fs));
            ("original_gamma", `String (Fmt.str "%a" Type_env.pp gamma)) ])
    (fun () ->
    if original_successor_alias_facts_prove ~matching existentials left_fs
         right_fs gamma
    then true
    else
    try check_entailment_simplified ~matching existentials left_fs right_fs gamma
    with
    | Reduction.ReductionException (_, "Invalid List Expression")
      when !Config.Verification.total
           && not !Config.under_approximation
           && SS.is_empty existentials ->
        (* Refuting a list domain can temporarily substitute an empty list into
           an already-defined head/tail fact. Eager reduction cannot evaluate that
           inconsistent alternative. Submit the original complete counterquery;
           do not discard the fact, assume a domain, or interpret the exception
           as UNSAT. Required SMT unknown still propagates from check_sat. *)
        let counterquery =
          Expr.Set.of_list
            (Expr.negate (Expr.conjunct right_fs) :: PFS.to_list left_fs)
        in
        Option.is_none (Smt.check_sat counterquery (Type_env.as_hashtbl gamma))
    )

let is_equal ?matching ~pfs ~gamma e1 e2 =
  (* let t = Unix.gettimeofday () in *)
  let feq =
    Reduction.reduce_lexpr ?matching ~gamma ~pfs (BinOp (e1, Equal, e2))
  in
  let result =
    match feq with
    | Lit (Bool b) -> b
    | BinOp (_, Equal, _) | BinOp (_, And, _) ->
        check_entailment ?matching SS.empty pfs [ feq ] gamma
    | _ ->
        raise
          (Failure
             ("Equality reduced to something unexpected: "
             ^ (Fmt.to_to_string Expr.pp) feq))
  in
  (* Utils.Statistics.update_statistics "FOS: is_equal" (Unix.gettimeofday () -. t); *)
  result

let is_different ~pfs ~gamma e1 e2 =
  (* let t = Unix.gettimeofday () in *)
  let feq =
    Reduction.reduce_lexpr ~gamma ~pfs (UnOp (Not, BinOp (e1, Equal, e2)))
  in
  let result =
    match feq with
    | Lit (Bool b) -> b
    | Expr.UnOp (Not, _) -> check_entailment SS.empty pfs [ feq ] gamma
    | _ ->
        raise
          (Failure
             ("Inequality reduced to something unexpected: "
             ^ (Fmt.to_to_string Expr.pp) feq))
  in
  (* Utils.Statistics.update_statistics "FOS: is different" (Unix.gettimeofday () -. t); *)
  result

let num_is_less_or_equal ~pfs ~gamma e1 e2 =
  let feq =
    Reduction.reduce_lexpr ~gamma ~pfs (Expr.BinOp (e1, FLessThanEqual, e2))
  in
  let result =
    match feq with
    | Lit (Bool b) -> b
    | BinOp (ra, Equal, rb) -> is_equal ~pfs ~gamma ra rb
    | BinOp (_, FLessThanEqual, _) ->
        check_entailment SS.empty pfs [ feq ] gamma
    | _ ->
        raise
          (Failure
             ("Inequality reduced to something unexpected: "
             ^ (Fmt.to_to_string Expr.pp) feq))
  in
  result

let resolve_loc_name ~pfs ~gamma loc =
  Logging.tmi (fun fmt -> fmt "get_loc_name: %a" Expr.pp loc);
  match Reduction.reduce_lexpr ~pfs ~gamma loc with
  | Lit (Loc loc) | ALoc loc -> Some loc
  | loc' -> Reduction.resolve_expr_to_location pfs gamma loc'
