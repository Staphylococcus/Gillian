(* Proof dependencies, including macros and nested logical conditionals. This
   first induction rule supports a single recursive lemma per component. *)
open Containers

type dependency = Lemma of string | Macro of string
type induction = { name : string; entry_rank : Expr.t }

let dependencies commands =
  let visitor =
    object
      inherit [_] Visitors.reduce
      method zero = []
      method plus = ( @ )
      method! visit_ApplyLem _ name _ _ = [ Lemma name ]
      method! visit_Macro _ name _ = [ Macro name ]
    end
  in
  List.concat_map (visitor#visit_lcmd ()) commands

let edges (prog : ('a, 'b) Prog.t) = function
  | Lemma name ->
      let lemma = Prog.get_lemma_exn prog name in
      dependencies (Option.value ~default:[] lemma.lemma_proof)
  | Macro name -> (
      match Macro.get prog.macros name with
      | Some macro -> dependencies macro.macro_definition
      | None -> Fmt.failwith "Unknown proof macro %s" name)

let recursive edges = function
  | [] -> false
  | [ node ] -> List.mem node (edges node)
  | _ -> true

let unsupported message =
  raise
    (Gillian_result.Exc.Gillian_error
       (OperationError
          ("Unsupported recursive lemma proof dependency: " ^ message)))

let variant (lemma : Lemma.t) =
  match lemma.lemma_variant with
  | None -> unsupported (lemma.lemma_name ^ " needs a variant.")
  | Some rank ->
      (* Restrict ranks to arguments, so call-site instantiation does not guess
         values of heap existentials or depend on a particular matched spec. *)
      let params = SS.of_list lemma.lemma_params in
      let lparams =
        SS.of_list (List.map (fun p -> "#" ^ p) lemma.lemma_params)
      in
      if
        (not (SS.subset (Expr.pvars rank) params))
        || (not (SS.subset (Expr.lvars rank) lparams))
        || not (SS.is_empty (Expr.alocs rank))
      then
        unsupported
          (lemma.lemma_name ^ " variant must depend only on its parameters.");
      rank

let recursive_lemmas prog name =
  let edges = edges prog in
  let components = Tarjan.tarjan (fun visit -> visit (Lemma name)) edges in
  (* A macro expansion must terminate independently of lemma induction. Even
     inside a ranked lemma component, a macro-only cycle is unsupported. *)
  let macros =
    List.concat components
    |> List.filter (function
         | Macro _ -> true
         | _ -> false)
  in
  let macro_edges node =
    List.filter
      (function
        | Macro _ -> true
        | _ -> false)
      (edges node)
  in
  let macro_components =
    Tarjan.tarjan (fun visit -> List.iter visit macros) macro_edges
  in
  if List.exists (recursive macro_edges) macro_components then
    unsupported "cyclic macro expansion.";
  List.fold_left
    (fun names component ->
      if not (recursive edges component) then names
      else
        match
          List.filter_map
            (function
              | Lemma name -> Some name
              | Macro _ -> None)
            component
        with
        | [ name ] ->
            ignore (variant (Prog.get_lemma_exn prog name));
            SS.add name names
        | _ ->
            unsupported "mutually recursive lemmas need a joint induction rule.")
    SS.empty components

let check_lemma ~proved ~induction prog name =
  let recursive = recursive_lemmas prog name in
  SS.iter
    (fun name ->
      if
        (not (SS.mem name proved))
        && not
             (Option.fold ~none:false
                ~some:(fun ctx -> ctx.name = name)
                induction)
      then
        unsupported
          (name
         ^ " has not been proved in this verification run. Select its proof as \
            well."))
    recursive

let instantiate_variant lemma args =
  let rank = variant lemma in
  let bindings =
    List.concat_map
      (fun (param, arg) ->
        [ (Expr.PVar param, arg); (Expr.LVar ("#" ^ param), arg) ])
      (List.combine lemma.Lemma.lemma_params args)
  in
  SVal.SESubst.subst_in_expr (SVal.SESubst.init bindings) ~partial:true rank

let nonnegative rank = Expr.BinOp (Expr.zero_i, ILessThanEqual, rank)
let decreases rank entry_rank = Expr.BinOp (rank, ILessThan, entry_rank)

(* Dependencies before their callers. Selection is preserved: unselected
   recursive summaries are rejected at use, never silently assumed proved. *)
let order_lemmas prog selected =
  Tarjan.tarjan
    (fun visit -> SS.iter (fun name -> visit (Lemma name)) selected)
    (edges prog)
  |> List.rev
  |> List.concat_map
       (List.filter_map (function
         | Lemma name when SS.mem name selected -> Some name
         | _ -> None))
