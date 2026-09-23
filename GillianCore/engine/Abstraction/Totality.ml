(* Checked total-correctness fragment of the compiled GIL program: ranked
   natural loops, resolved calls and natural-ranked self recursion.
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

(* A finite integral binary64 value denotes an exact mathematical integer.
   Strict IEEE comparison on these values agrees with natural-number order.
   Arithmetic remains binary64: stalled/rounded updates must still prove descent. *)
let natural_rank typ rank =
  match typ with
  | Type.IntType -> ProofDependencies.nonnegative rank
  | NumberType ->
      Expr.BinOp
        ( Expr.UnOp (IsInt, rank),
          And,
          Expr.BinOp (Lit (Num 0.), FLessThanEqual, rank) )
  | _ -> Expr.Lit (Bool false)

let rank_decreases typ rank entry =
  match typ with
  | Type.IntType -> ProofDependencies.decreases rank entry
  | NumberType -> Expr.BinOp (rank, FLessThan, entry)
  | _ -> Expr.Lit (Bool false)

(* Check operator domains before reduction can erase their results.
   Proof values can contain symbolic identities; executable syntax cannot.
   Short-circuit operands are required only on their evaluated paths. *)
let check_expression ?(proof = false) ~require ~proves ~evaluate expr =
  let typ e t = Expr.BinOp (UnOp (TypeOf, e), Equal, Lit (Type t)) in
  let nonnegative e = Expr.BinOp (Lit (Int Z.zero), ILessThanEqual, e) in
  let length e = Expr.UnOp (LstLen, e) in
  let bounded e =
    Expr.BinOp (e, ILessThanEqual, Lit (Int (Z.of_int max_int)))
  in
  let rec check guard expr =
    let need condition = require expr (Expr.BinOp (guard, Impl, condition)) in
    let children xs = List.iter (check guard) xs in
    match expr with
    | Expr.Lit (Loc loc)
      when !Config.Verification.closed_entry && Names.is_lloc_name loc ->
        unsupported "closed entry cannot name a generated concrete location."
    | Expr.Lit (Constant c) when Option.is_none (Literal.static_constant c) ->
        unsupported "nondeterministic runtime constants need an explicit model."
    | Expr.BinOp (left, ((And | Or | Impl) as op), right) ->
        check guard left;
        need (typ left BooleanType);
        let condition = if op = Or then Expr.UnOp (Not, left) else left in
        let branch = Expr.BinOp (guard, And, condition) in
        if not (proves (Expr.UnOp (Not, branch))) then (
          check branch right;
          require expr (Expr.BinOp (branch, Impl, typ right BooleanType)))
    | BinOp (list, LstNth, index) ->
        children [ list; index ];
        List.iter need
          [
            typ list ListType;
            typ index IntType;
            nonnegative index;
            bounded index;
            Expr.BinOp (index, ILessThan, length list);
          ]
    | BinOp (value, LstRepeat, count) ->
        children [ value; count ];
        List.iter need [ typ count IntType; nonnegative count; bounded count ]
    | UnOp ((Car | Cdr), list) ->
        check guard list;
        List.iter need
          [
            typ list ListType;
            Expr.BinOp (Lit (Int Z.zero), ILessThan, length list);
          ]
    | LstSub (list, start, count) ->
        children [ list; start; count ];
        List.iter need
          [
            typ list ListType;
            typ start IntType;
            typ count IntType;
            nonnegative start;
            nonnegative count;
            bounded start;
            bounded count;
            Expr.BinOp
              (Expr.BinOp (start, IPlus, count), ILessThanEqual, length list);
          ]
    | BinOp (string, StrNth, index) ->
        children [ string; index ];
        List.iter need
          [
            typ string StringType;
            typ index NumberType;
            Expr.UnOp (IsInt, index);
            Expr.BinOp (Lit (Num 0.), FLessThanEqual, index);
          ];
        let offset =
          match evaluate index with
          | Expr.Lit (Num n) when Float.is_finite n && Float.is_integer n ->
              Expr.Lit (Int (Z.of_float n))
          | _ ->
              unsupported
                "symbolic byte indexing needs a checked numeric/index bridge."
        in
        List.iter need
          [
            bounded offset;
            Expr.BinOp
              (offset, ILessThan, length (Expr.UnOp (StrToBytes, string)));
          ]
    | BinOp (left, (IDiv | IMod), right) ->
        children [ left; right ];
        List.iter need
          [
            typ left IntType;
            typ right IntType;
            Expr.UnOp (Not, Expr.BinOp (right, Equal, Lit (Int Z.zero)));
          ]
    | UnOp (op, e) -> (
        check guard e;
        match op with
        | TypeOf -> ()
        | Not -> need (typ e BooleanType)
        | IUnaryMinus | IntToNum -> need (typ e IntType)
        | StrLen | StrToBytes | ToNumberOp -> need (typ e StringType)
        | Utf16Len -> need (typ e Utf16Type)
        | LstLen | LstRev -> need (typ e ListType)
        | NumToInt ->
            List.iter need
              [
                typ e NumberType;
                Expr.BinOp (Lit (Num (-.Float.max_float)), FLessThanEqual, e);
                Expr.BinOp (e, FLessThanEqual, Lit (Num Float.max_float));
              ]
        | SetToList -> unsupported "set expressions in executable code."
        | Car | Cdr -> assert false
        | FUnaryMinus
        | BitwiseNot
        | M_abs
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
        | ToStringOp
        | ToIntOp
        | ToUint16Op
        | ToInt32Op
        | ToUint32Op
        | IsInt
        | M_isNaN -> need (typ e NumberType))
    | BinOp (left, op, right) -> (
        children [ left; right ];
        let both t = List.iter need [ typ left t; typ right t ] in
        match op with
        | Equal | ValueEqual -> ()
        | IPlus
        | IMinus
        | ITimes
        | ILessThan
        | ILessThanEqual
        | BitwiseAnd
        | BitwiseOr
        | BitwiseXor
        | BitwiseAndL
        | BitwiseOrL
        | BitwiseXorL -> both IntType
        | LeftShift
        | SignedRightShift
        | UnsignedRightShift
        | LeftShiftL
        | SignedRightShiftL
        | UnsignedRightShiftL ->
            both IntType;
            unsupported "integer shift domains are not yet checked."
        | StrCat | StrLess -> both StringType
        | Utf16Cat -> both Utf16Type
        | FPlus
        | FMinus
        | FTimes
        | FDiv
        | FMod
        | FLessThan
        | FLessThanEqual
        | BitwiseAndF
        | BitwiseOrF
        | BitwiseXorF
        | LeftShiftF
        | SignedRightShiftF
        | UnsignedRightShiftF
        | M_atan2
        | M_pow -> both NumberType
        | SetMem when proof -> need (typ right SetType)
        | (SetSub | SetDiff) when proof -> both SetType
        | SetMem | SetSub | SetDiff ->
            unsupported "set expressions in executable code."
        | And | Or | Impl | LstNth | LstRepeat | StrNth | IDiv | IMod ->
            assert false)
    | NOp (LstCat, xs) ->
        children xs;
        List.iter (fun x -> need (typ x ListType)) xs
    | NOp (SetUnion, xs) when proof ->
        children xs;
        List.iter (fun x -> need (typ x SetType)) xs
    | ESet xs when proof -> children xs
    | EList xs -> children xs
    | Lit _ | PVar _ -> ()
    | (LVar _ | ALoc _) when proof -> ()
    | NOp _
    | ESet _
    | ConstructorApp _
    | FuncApp _
    | LVar _
    | ALoc _
    | ForAll _
    | Exists _
    | Cases _ -> unsupported "logical-only expressions in executable code."
  in
  check (Expr.Lit (Bool true)) expr

(* Share domain rules with executed expressions, without changing legacy proof
   evaluation or assuming a missing domain to make a proof go through. *)
let check_proof_expression ~context ~evaluate ~assertion expr =
  if !Config.Verification.total then
    let proves condition = assertion (evaluate condition) in
    check_expression ~proof:true ~proves ~evaluate
      ~require:(fun partial condition ->
        if not (proves condition) then
          raise
            (Gillian_result.Exc.analysis_failure
               (Fmt.str "%s is not proved defined: %a" context Expr.pp partial)))
      expr

(* Attach obligations before any assertion rewriting or automatic unfolding.
   Keeping original facts also lets producers establish domains without using
   the unchecked expression's own (possibly simplified) assumption. *)
let preserve_assertion_domains a =
  if not !Config.Verification.total then a
  else
    let value e = Asrt.definedness ~fact:false e in
    let fact e = Asrt.definedness ~fact:true e in
    let obligations =
      List.concat_map
        (function
          | a when Option.is_some (Asrt.as_definedness a) ->
              unsupported
                "internal definedness obligations in input assertions."
          | Asrt.Emp -> []
          | Pure e -> [ fact e ]
          | Types ets ->
              List.map
                (fun (e, t) ->
                  fact (Expr.BinOp (UnOp (TypeOf, e), Equal, Lit (Type t))))
                ets
          | CorePred (_, ins, outs) -> List.map value (ins @ outs)
          | Wand { lhs = _, lhs; rhs = _, rhs } -> List.map value (lhs @ rhs))
        a
    in
    List.sort_uniq Stdlib.compare obligations @ a

exception Pending_domain of Expr.t

(* Work on a disposable state. Only independently defined original facts may
   enter the domain context; an unchecked fact cannot justify itself or another
   unchecked fact. A contradictory checked fact is genuine infeasibility. *)
let check_assertion_production ~evaluate ~assertion ~assume state a =
  if !Config.Verification.total then
    let obligations = List.filter_map Asrt.as_definedness a in
    let facts, values = List.partition fst obligations in
    let check state (fact, e) =
      let proves c = assertion state (evaluate state c) in
      check_expression ~proof:true ~proves ~evaluate:(evaluate state)
        ~require:(fun partial condition ->
          if not (proves condition) then raise (Pending_domain partial))
        (if fact then Expr.UnOp (Not, e) else e)
    in
    let rec establish state pending =
      let ready, deferred =
        List.fold_left
          (fun (ready, deferred) ((_, e) as obligation) ->
            try
              check state obligation;
              (* A defined fact already reduced to true adds no information.
                 Avoid rechecking consistency of the entire scratch context for
                 batches of such facts (common in matched predicate outputs). *)
              if Expr.equal (evaluate state e) Expr.true_ then (ready, deferred)
              else (e :: ready, deferred)
            with Pending_domain _ -> (ready, obligation :: deferred))
          ([], []) pending
      in
      if ready = [] then List.iter (check state) (List.rev deferred @ values)
      else
        (* Batch independently checked facts: no pending fact enters the context,
           and one consistency query suffices for this round. *)
        match assume state (List.rev ready) with
        | None -> ()
        | Some state -> establish state (List.rev deferred)
    in
    try establish state facts
    with Pending_domain e ->
      raise
        (Gillian_result.Exc.analysis_failure
           (Fmt.str "Produced assertion is not proved defined: %a" Expr.pp e))

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

(* Derive a natural-loop hierarchy from the actual GIL control flow. Each
   cyclic component has one entry through a ranked invariant. Removing that
   header leaves only acyclic paths or recursively checked inner components. *)
let prepare_loops
    ?(defer_cycle = fun _ message -> unsupported message)
    ~set_loop_info
    ~macros
    ~predecessors
    (proc : ('a, int) Proc.t) =
  let body = proc.proc_body in
  let length = Array.length body in
  if length = 0 then unsupported (proc.proc_name ^ " has no body.");
  let successors i =
    let _, _, cmd = body.(i) in
    (* Runtime helpers end impossible cases with assume(false). This command
       remains forbidden if reached; it has no executable fall-through to
       analyse, and cannot justify dropping a feasible path. *)
    let next =
      match cmd with
      | Cmd.Logic (Assume (Lit (Bool false))) -> []
      | _ -> Cmd.successors cmd i
    in
    if List.exists (fun j -> j < 0 || j >= length) next then
      unsupported (proc.proc_name ^ " has a control-flow edge outside its body.");
    next
  in
  (* Frame only locals whose value cannot change observably across iterations.
     A modified live local must be generalized by the invariant, otherwise an
     exit can retain its concrete first-entry value and yield a false proof. *)
  let rec logic_reads seen cmd =
    let direct = Cmd.pvars (Logic cmd) in
    let calls = ProofDependencies.dependencies [ cmd ] in
    List.fold_left
      (fun reads -> function
        | ProofDependencies.Lemma _ -> reads
        | Macro name when SS.mem name seen -> reads
        | Macro name -> (
            match Macro.get macros name with
            | None -> reads
            | Some macro ->
                List.fold_left
                  (fun reads cmd ->
                    SS.union reads (logic_reads (SS.add name seen) cmd))
                  reads macro.macro_definition))
      direct calls
  in
  let expressions es =
    List.fold_left (fun acc e -> SS.union acc (Expr.pvars e)) SS.empty es
  in
  let accesses (_, _, cmd) =
    match cmd with
    | Cmd.Assignment (x, e) -> (SS.singleton x, Expr.pvars e)
    | LAction (x, _, es) -> (SS.singleton x, expressions es)
    | Arguments x -> (SS.singleton x, SS.empty)
    | PhiAssignment phis -> (SS.of_list (List.map fst phis), SS.empty)
    | Call ({ var_name; fun_name; args; bindings }, _) ->
        let binding_exprs =
          Option.fold ~none:[] ~some:(fun (_, bs) -> List.map snd bs) bindings
        in
        (SS.singleton var_name, expressions ((fun_name :: args) @ binding_exprs))
    | Logic cmd -> (SS.empty, logic_reads SS.empty cmd)
    | _ -> (SS.empty, Cmd.pvars cmd)
  in
  let accesses = Array.map accesses body in
  (* PHI operands are selected by the actual incoming edge. Reading every
     alternative would invent live, uninitialised locals on other branches. *)
  let phi_reads previous index =
    match body.(index) with
    | _, _, PhiAssignment phis ->
        let selected =
          match
            Hashtbl.find_opt predecessors (proc.proc_name, previous, index)
          with
          | Some selected -> selected
          | None ->
              unsupported
                (proc.proc_name ^ " has a PHI without its predecessor index.")
        in
        snd
          (List.fold_left
             (fun (written, read) (x, values) ->
               let value =
                 match List.nth_opt values selected with
                 | Some value -> value
                 | None ->
                     unsupported
                       (proc.proc_name
                      ^ " has a PHI without its incoming value.")
               in
               ( SS.add x written,
                 SS.union read (SS.diff (Expr.pvars value) written) ))
             (SS.empty, SS.empty) phis)
    | _ -> SS.empty
  in
  let live = Array.make length SS.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = length - 1 downto 0 do
      let written, read = accesses.(i) in
      let after =
        List.fold_left
          (fun acc j -> SS.union acc (SS.union live.(j) (phi_reads i j)))
          SS.empty (successors i)
      in
      let before = SS.union read (SS.diff after written) in
      if not (SS.equal before live.(i)) then (
        live.(i) <- before;
        changed := true)
    done
  done;
  let cyclic successors = function
    | [ i ] -> List.mem i (successors i)
    | [] -> false
    | _ -> true
  in
  let loop_ids = Array.make length [] in
  let headers = Hashtbl.create 0 in
  let ranked i =
    match body.(i) with
    | _, _, Logic (SL (Invariant (_, _, Some _))) -> true
    | _ -> false
  in
  let rec discover parents nodes =
    let edges i = List.filter (fun j -> List.mem j nodes) (successors i) in
    let components =
      Tarjan.tarjan (fun visit -> List.iter visit nodes) edges
      |> List.filter (cyclic edges)
    in
    List.iter
      (fun members ->
        let entries = ref (if List.mem 0 members then [ 0 ] else []) in
        Array.iteri
          (fun i _ ->
            if not (List.mem i members) then
              List.iter
                (fun j -> if List.mem j members then entries := j :: !entries)
                (successors i))
          body;
        let entries = List.sort_uniq Int.compare !entries in
        let candidates = List.filter ranked members in
        let rec after_phis seen i =
          if List.mem i seen || not (List.mem i members) then None
          else if ranked i then Some i
          else
            match (body.(i), successors i) with
            | (_, _, PhiAssignment _), [ next ] -> after_phis (i :: seen) next
            | _ -> None
        in
        let entry_header =
          match entries with
          | [ entry ] -> after_phis [] entry
          | _ -> None
        in
        let header =
          match (entry_header, entries, candidates) with
          | Some header, _, _ -> Some header
          | _, [], [ header ] -> Some header
          | _, _, [] ->
              defer_cycle members
                (proc.proc_name
               ^ " has a control-flow cycle without a ranked invariant header."
                );
              None
          | _ ->
              unsupported
                (proc.proc_name ^ " has an entry bypassing its ranked header.")
        in
        Option.iter
          (fun header ->
            let ids =
              (proc.proc_name ^ "#ranked-loop-" ^ string_of_int header)
              :: parents
            in
            Hashtbl.add headers header members;
            List.iter (fun i -> loop_ids.(i) <- ids) members;
            discover ids (List.filter (( <> ) header) members))
          header)
      components
  in
  discover [] (List.init length Fun.id);
  let body =
    Array.mapi
      (fun i (annot, label, cmd) ->
        let cmd =
          match cmd with
          | Cmd.Logic (SL (Invariant (a, binders, Some rank)))
            when Hashtbl.mem headers i ->
              let members = Hashtbl.find headers i in
              let written =
                List.fold_left
                  (fun acc j -> SS.union acc (fst accesses.(j)))
                  SS.empty members
              in
              let carried = SS.inter written live.(i) in
              (* Havoc modified live locals with the existing invariant binder
               mechanism. Assertions still constrain their abstract values. *)
              let binders =
                SS.elements (SS.union carried (SS.of_list binders))
              in
              if
                (not (SS.subset (Expr.pvars rank) (Asrt.pvars a)))
                || (not
                      (SS.subset (Expr.lvars rank)
                         (SS.inter (Asrt.lvars a) (SS.of_list binders))))
                || not (SS.is_empty (Expr.alocs rank))
              then
                unsupported
                  (proc.proc_name
                 ^ " loop variant must use only program variables or logical \
                    binders captured by its invariant.");
              Cmd.Logic (SL (Invariant (a, binders, Some rank)))
          | Logic (SL (Invariant _)) ->
              unsupported
                (proc.proc_name
               ^ " contains an operation outside the totality fragment: \
                  invariant.")
          | _ -> cmd
        in
        (set_loop_info loop_ids.(i) annot, label, cmd))
      body
  in
  { proc with proc_body = body }

(* Imported/unannotated helper bodies may be executed in full. This never
   licenses their existing (possibly partial or trusted) summaries. *)
let inline_body (proc : ('a, 'b) Proc.t) =
  match proc.proc_spec with
  | None -> true
  | Some spec -> not spec.spec_to_verify

let check_command ~is_action_total name (cmd : int Cmd.t) =
  match cmd with
  | Cmd.Call ({ fun_name = Lit (String callee); args; _ }, _) ->
      Some (callee, List.length args)
  | LAction (_, action, args) ->
      if not (is_action_total action (List.length args)) then
        unsupported
          (Fmt.str "%s uses an uncertified primitive action: %s/%d" name action
             (List.length args));
      None
  | Call _
  | Skip
  | Assignment _
  | Goto _
  | GuardedGoto _
  | Arguments _
  | PhiAssignment _
  | ReturnNormal
  | ReturnError
  | Fail _
  | Logic
      ( Assert _ | If _ | Macro _
      | SL (ApplyLem _ | Fold _ | Unfold _ | GUnfold _ | SepAssert _) )
  | Logic (SL (Invariant (_, _, Some _))) -> None
  | _ ->
      unsupported
        (Fmt.str "%s contains an operation outside the totality fragment: %a"
           name Cmd.pp_indexed cmd)

let body_calls ~is_action_total (proc : ('a, int) Proc.t) =
  Array.to_list proc.proc_body
  |> List.filter_map (fun (_, _, cmd) ->
         check_command ~is_action_total proc.proc_name cmd)

let check_macro prog name =
  let edges name =
    match Macro.get prog.Prog.macros name with
    | None -> unsupported ("missing proof macro " ^ name)
    | Some macro ->
        ProofDependencies.dependencies macro.macro_definition
        |> List.filter_map (function
             | ProofDependencies.Macro name -> Some name
             | Lemma _ -> None)
  in
  let components = Tarjan.tarjan (fun visit -> visit name) edges in
  if List.exists (ProofDependencies.recursive edges) components then
    unsupported "cyclic proof macro expansion."

let check_closed_logic cmd =
  if !Config.Verification.closed_entry then
    match cmd with
    | LCmd.Assert _ | If _ | Macro _ | SL (GUnfold _) -> ()
    | _ ->
        unsupported
          (Fmt.str "closed entry cannot abstract or assume heap resources: %a"
             LCmd.pp cmd)

let check_logic cmd =
  check_closed_logic cmd;
  match cmd with
  | LCmd.Assert _ | If _ | Macro _
  | SL (ApplyLem _ | Fold _ | Unfold _ | GUnfold _ | SepAssert _) -> ()
  | cmd ->
      unsupported
        (Fmt.str "reached a proof operation outside the totality fragment: %a"
           LCmd.pp cmd)

let order_procs
    ~is_action_total
    ~set_loop_info
    (prog : ('a, int) Prog.t)
    selected =
  if SS.is_empty selected then unsupported "select at least one procedure.";
  let calls = Hashtbl.create 0 in
  SS.iter
    (fun name ->
      let proc =
        match Prog.get_proc prog name with
        | Some p -> p
        | None -> unsupported (name ^ " has no body.")
      in
      let proc =
        prepare_loops ~set_loop_info ~macros:prog.macros
          ~predecessors:prog.predecessors proc
      in
      Hashtbl.replace prog.procs name proc;
      let spec = spec proc in
      let rank = variant spec in
      let callees = body_calls ~is_action_total proc in
      if
        SS.cardinal (SS.of_list proc.proc_params)
        <> List.length proc.proc_params
      then unsupported (name ^ " has duplicate formal parameters.");
      List.iter
        (fun (callee, arity) ->
          let target =
            match Prog.get_proc prog callee with
            | Some p -> p
            | None -> unsupported (callee ^ " has no body.")
          in
          if SS.mem callee selected then (
            if arity <> List.length target.proc_params then
              unsupported
                (callee
               ^ " requires exact call arity in the current totality fragment."
                ))
          else if not (inline_body target) then
            unsupported
              (callee
             ^ " must be selected and proved total along with its caller."))
        callees;
      let callees =
        List.map fst callees |> List.filter (fun n -> SS.mem n selected)
      in
      if List.mem name callees && Option.is_none rank then
        unsupported (name ^ " needs a recursive-call variant.");
      Hashtbl.add calls name callees)
    selected;
  (* Explicit edges only schedule selected proofs. The interpreter still resolves
     each actual target and checks its proved status, arity and precondition. *)
  List.iter
    (fun (caller, callee) ->
      if not (SS.mem caller selected && SS.mem callee selected) then
        unsupported
          "proof dependencies require both caller and callee to be selected.";
      if caller = callee then
        unsupported "proof dependencies cannot order a procedure before itself.";
      Hashtbl.replace calls caller (callee :: Hashtbl.find calls caller))
    !Config.Verification.proof_dependencies;
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
