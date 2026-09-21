(* Initial total-correctness fragment of the compiled GIL program: acyclic
   procedure control flow, direct calls and natural-ranked self recursion.
   Unsupported operations are rejected, never treated as termination axioms. *)
open Containers

type context = {
  name : string;
  variant : Expr.t option;
  entry_rank : Expr.t option;
}

let unsupported message =
  raise
    (Gillian_result.Exc.Gillian_error
       (OperationError ("Unsupported totality proof: " ^ message)))

let spec (proc : ('a, 'b) Proc.t) =
  match proc.proc_spec with
  | Some spec
    when spec.spec_to_verify && (not spec.spec_incomplete)
         && spec.spec_sspecs <> []
         && List.for_all (fun (s : Spec.st) -> s.ss_to_verify) spec.spec_sspecs
         && spec.spec_params = proc.proc_params -> spec
  | _ ->
      unsupported
        (proc.proc_name
       ^ " requires a complete specification with every case checked.")

let variant (spec : Spec.t) =
  let rank = (List.hd spec.spec_sspecs).ss_variant in
  if
    not
      (List.for_all
         (fun (s : Spec.st) -> Option.equal Expr.equal rank s.ss_variant)
         spec.spec_sspecs)
  then
    unsupported
      (spec.spec_name ^ " needs the same variant in every specification case.");
  Option.iter
    (fun rank ->
      if
        (not (SS.subset (Expr.pvars rank) (SS.of_list spec.spec_params)))
        || (not (SS.is_empty (Expr.lvars rank)))
        || not (SS.is_empty (Expr.alocs rank))
      then
        unsupported
          (spec.spec_name ^ " variant must use only formal program parameters."))
    rank;
  rank

let body_calls ~is_action_total (proc : ('a, int) Proc.t) =
  let body = proc.proc_body in
  let length = Array.length body in
  if length = 0 then unsupported (proc.proc_name ^ " has no body.");
  let successors i =
    let _, _, cmd = body.(i) in
    let next = Cmd.successors cmd i in
    if List.exists (fun j -> j < 0 || j >= length) next then
      unsupported (proc.proc_name ^ " has a control-flow edge outside its body.");
    next
  in
  let components =
    Tarjan.tarjan
      (fun visit -> Array.iteri (fun i _ -> visit i) body)
      successors
  in
  if
    List.exists
      (function
        | [ i ] -> List.mem i (successors i)
        | [] -> false
        | _ -> true)
      components
  then
    unsupported
      (proc.proc_name
     ^ " has a control-flow cycle; loop progress is not yet checked.");
  Array.to_list body
  |> List.filter_map (fun (_, _, cmd) ->
         match cmd with
         | Cmd.Call ({ fun_name = Lit (String name); args; _ }, _) ->
             Some (name, List.length args)
         | LAction (_, name, args) ->
             if not (is_action_total name (List.length args)) then
               unsupported
                 (Fmt.str "%s uses an uncertified primitive action: %s/%d"
                    proc.proc_name name (List.length args));
             None
         | Skip
         | Assignment _
         | Goto _
         | GuardedGoto _
         | Arguments _
         | PhiAssignment _
         | ReturnNormal
         | ReturnError
         | Fail _
         | Logic (Assert _) -> None
         | _ ->
             unsupported
               (Fmt.str
                  "%s contains an operation outside the totality fragment: %a"
                  proc.proc_name Cmd.pp_indexed cmd))

let order_procs ~is_action_total (prog : ('a, int) Prog.t) selected =
  if SS.is_empty selected then unsupported "select at least one procedure.";
  let calls = Hashtbl.create 0 in
  SS.iter
    (fun name ->
      let proc =
        match Prog.get_proc prog name with
        | Some p -> p
        | None -> unsupported (name ^ " has no body.")
      in
      let spec = spec proc in
      let rank = variant spec in
      let callees = body_calls ~is_action_total proc in
      if
        SS.cardinal (SS.of_list proc.proc_params)
        <> List.length proc.proc_params
      then unsupported (name ^ " has duplicate formal parameters.");
      List.iter
        (fun (callee, arity) ->
          if not (SS.mem callee selected) then
            unsupported
              (callee
             ^ " must be selected and proved total along with its caller.");
          let target = Prog.get_proc_exn prog callee in
          if arity <> List.length target.proc_params then
            unsupported
              (callee
             ^ " requires exact call arity in the current totality fragment."))
        callees;
      let callees = List.map fst callees in
      if List.mem name callees && Option.is_none rank then
        unsupported (name ^ " needs a recursive-call variant.");
      Hashtbl.add calls name callees)
    selected;
  let components =
    Tarjan.tarjan (fun visit -> SS.iter visit selected) (Hashtbl.find calls)
  in
  if List.exists (fun c -> List.length c > 1) components then
    unsupported "mutually recursive procedures need a joint termination rule.";
  List.concat (List.rev components)

let call_rank ctx params args =
  match (ctx.variant, ctx.entry_rank) with
  | Some rank, Some entry_rank ->
      let subst =
        SVal.SESubst.init
          (List.map2 (fun name arg -> (Expr.PVar name, arg)) params args)
      in
      (SVal.SESubst.subst_in_expr subst ~partial:true rank, entry_rank)
  | _ -> unsupported (ctx.name ^ " has no checked entry measure.")
