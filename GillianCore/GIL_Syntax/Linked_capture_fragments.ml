(* Schema4 container fragmentation. No normalization and no verifier injection.
   emit carries tagged bounded leaves; take returns untagged bounded leaves.
   The parent accounting pass includes original list spines and occurrences.
   Its depth contract differs explicitly from V3: only emitted typed leaves
   retain physical depth2048. Reassembled records are passive/discarded. *)
module K = Linked_capture_codec
let require = K.require
let fail why = raise (K.Incomplete why)
type output = string -> string list -> Yojson.Safe.t -> unit
type input = string -> string list -> Yojson.Safe.t
let pred_to_yojson = TypeDef__.pred_to_yojson
type write = { emit:output; allowed:Obj.t list ref }
type read = { take:input; allowed:Obj.t list ref }
let at route f =
  try f () with K.Incomplete why ->
    let field = List.filteri (fun i _ -> i >= 4) route in
    raise (K.Incomplete (why ^ " fragmentRoute=" ^
      String.concat "/" (List.map K.hex (if field=[] then route else field))))
let jstring s = `String s
let string_of = function `String s -> Ok s | _ -> Error "string"
let jint n = `Int n
let int_of = function `Int n -> Ok n | _ -> Error "int"
let jbool b = `Bool b
let bool_of = function `Bool b -> Ok b | _ -> Error "bool"
let expr_guard allowed value =
  K.guard_ast_v3 (fun v x -> v#visit_expr () x) value;
  allowed := List.rev_append
    (K.inspect ~node_limit:131072 ~depth_limit:2048 value) !allowed
let write_leaf w guard to_json of_json route value = at route (fun () ->
  w.emit "fragment-field" route (K.checked_v4 ~guard ~to_json ~of_json value))
let read_leaf r guard to_json of_json route = at route (fun () ->
  let json = r.take "fragment-field" route in
  match of_json json with
  | Error why -> fail ("fragment decoder: " ^ why)
  | Ok value ->
      let wire = K.checked_v4 ~guard ~to_json ~of_json value in
      require (K.equal json (K.untag wire)) "fragment typed identity";
      value)
let ws w = write_leaf w K.guard_plain jstring string_of
let rs r = read_leaf r K.guard_plain jstring string_of
let wi w = write_leaf w K.guard_plain jint int_of
let ri r = read_leaf r K.guard_plain jint int_of
let wb w = write_leaf w K.guard_plain jbool bool_of
let rb r = read_leaf r K.guard_plain jbool bool_of
let we w = write_leaf w (expr_guard w.allowed) Expr.to_yojson Expr.of_yojson
let re r = read_leaf r (expr_guard r.allowed) Expr.to_yojson Expr.of_yojson
let wt w = write_leaf w K.guard_plain TypeDef__.typ_to_yojson TypeDef__.typ_of_yojson
let rt r = read_leaf r K.guard_plain TypeDef__.typ_to_yojson TypeDef__.typ_of_yojson
let wl w = write_leaf w K.guard_plain TypeDef__.location_to_yojson TypeDef__.location_of_yojson
let rl r = read_leaf r K.guard_plain TypeDef__.location_to_yojson TypeDef__.location_of_yojson
let wf w = write_leaf w K.guard_plain TypeDef__.flag_to_yojson TypeDef__.flag_of_yojson
let rf r = read_leaf r K.guard_plain TypeDef__.flag_to_yojson TypeDef__.flag_of_yojson
let write_list w item route xs =
  wi w route (List.length xs);
  List.iteri (fun i x -> item w (route@[string_of_int i]) x) xs
let read_list r item route =
  let n = ri r route in require (n>=0 && n<=131072) "fragment child count";
  let rec loop i acc =
    if i=n then List.rev acc
    else let x=item r (route@[string_of_int i]) in loop (i+1) (x::acc)
  in loop 0 []
let write_option w item route = function
  | None -> wb w route false
  | Some x -> wb w route true; item w (route@["some"]) x
let read_option r item route =
  if rb r route then Some (item r (route@["some"])) else None
let write_label w route (name,existentials) =
  ws w (route@["name"]) name;
  write_list w ws (route@["existentials"]) existentials
let read_label r route =
  let name=rs r (route@["name"]) in
  let existentials=read_list r rs (route@["existentials"]) in name,existentials
let write_param w route (name,typ) =
  ws w (route@["name"]) name; write_option w wt (route@["type"]) typ
let read_param r route =
  let name=rs r (route@["name"]) in
  let typ=read_option r rt (route@["type"]) in name,typ
let write_type_pair w route (expr,typ) =
  we w (route@["expr"]) expr; wt w (route@["type"]) typ
let read_type_pair r route =
  let expr=re r (route@["expr"]) in let typ=rt r (route@["type"]) in expr,typ
let write_atom w route (atom:TypeDef__.assertion_atom) =
  match atom with
  | TypeDef__.Emp -> ws w route "Emp"
  | TypeDef__.Pure expr -> ws w route "Pure"; we w (route@["expr"]) expr
  | TypeDef__.Types pairs -> ws w route "Types"; write_list w write_type_pair (route@["pairs"]) pairs
  | TypeDef__.CorePred (name,ins,outs) ->
      ws w route "CorePred";ws w (route@["name"]) name;
      write_list w we (route@["ins"]) ins;write_list w we (route@["outs"]) outs
  | TypeDef__.Wand {lhs=(lname,largs);rhs=(rname,rargs)} ->
      ws w route "Wand";ws w (route@["lhs-name"]) lname;
      write_list w we (route@["lhs-args"]) largs;ws w (route@["rhs-name"]) rname;
      write_list w we (route@["rhs-args"]) rargs
let read_atom r route : TypeDef__.assertion_atom =
  match rs r route with
  | "Emp" -> TypeDef__.Emp
  | "Pure" -> let expr=re r (route@["expr"]) in TypeDef__.Pure expr
  | "Types" -> let pairs=read_list r read_type_pair (route@["pairs"]) in TypeDef__.Types pairs
  | "CorePred" ->
      let name=rs r (route@["name"]) in
      let ins=read_list r re (route@["ins"]) in
      let outs=read_list r re (route@["outs"]) in TypeDef__.CorePred(name,ins,outs)
  | "Wand" ->
      let lname=rs r (route@["lhs-name"]) in
      let largs=read_list r re (route@["lhs-args"]) in
      let rname=rs r (route@["rhs-name"]) in
      let rargs=read_list r re (route@["rhs-args"]) in
      TypeDef__.Wand {lhs=(lname,largs);rhs=(rname,rargs)}
  | _ -> fail "fragment assertion constructor"
let write_assertion w = write_list w write_atom
let read_assertion r = read_list r read_atom
let write_located w route (assertion,location) =
  ws w route "located";
  write_assertion w (route@["assertion"]) assertion;
  write_option w wl (route@["location"]) location
let read_located r route =
  require (rs r route="located") "fragment located marker";
  let assertion=read_assertion r (route@["assertion"]) in
  let location=read_option r rl (route@["location"]) in assertion,location
let write_definition w route (label,assertion) =
  write_option w write_label (route@["label"]) label;
  write_assertion w (route@["assertion"]) assertion
let read_definition r route =
  let label=read_option r read_label (route@["label"]) in
  let assertion=read_assertion r (route@["assertion"]) in label,assertion
let write_scope w route (b:TypeDef__.verifier_scope_binding) =
  we w (route@["vsb_source"]) b.vsb_source;we w (route@["vsb_target"]) b.vsb_target
let read_scope r route : TypeDef__.verifier_scope_binding =
  let vsb_source=re r (route@["vsb_source"]) in
  let vsb_target=re r (route@["vsb_target"]) in {vsb_source;vsb_target}
let write_single w route (s:TypeDef__.single_spec) =
  write_located w (route@["ss_pre"]) s.ss_pre;
  write_list w write_located (route@["ss_posts"]) s.ss_posts;
  write_option w we (route@["ss_variant"]) s.ss_variant;
  write_option w write_scope (route@["ss_verifier_scope"]) s.ss_verifier_scope;
  wf w (route@["ss_flag"]) s.ss_flag;wb w (route@["ss_to_verify"]) s.ss_to_verify;
  write_option w write_label (route@["ss_label"]) s.ss_label
let read_single r route : TypeDef__.single_spec =
  let ss_pre=read_located r (route@["ss_pre"]) in
  let ss_posts=read_list r read_located (route@["ss_posts"]) in
  let ss_variant=read_option r re (route@["ss_variant"]) in
  let ss_verifier_scope=read_option r read_scope (route@["ss_verifier_scope"]) in
  let ss_flag=rf r (route@["ss_flag"]) in
  let ss_to_verify=rb r (route@["ss_to_verify"]) in
  let ss_label=read_option r read_label (route@["ss_label"]) in
  {ss_pre;ss_posts;ss_variant;ss_verifier_scope;ss_flag;ss_to_verify;ss_label}
let write_spec w route (s:TypeDef__.spec) =
  ws w (route@["spec_name"]) s.spec_name;
  write_list w ws (route@["spec_params"]) s.spec_params;
  write_option w (fun w route -> write_list w ws route) (route@["spec_raw_args"]) s.spec_raw_args;
  write_list w write_single (route@["spec_sspecs"]) s.spec_sspecs;
  wb w (route@["spec_normalised"]) s.spec_normalised;
  wb w (route@["spec_incomplete"]) s.spec_incomplete;
  wb w (route@["spec_to_verify"]) s.spec_to_verify;
  write_option w wl (route@["spec_location"]) s.spec_location
let read_spec r route : TypeDef__.spec =
  let spec_name=rs r (route@["spec_name"]) in
  let spec_params=read_list r rs (route@["spec_params"]) in
  let spec_raw_args=read_option r (fun r route -> read_list r rs route) (route@["spec_raw_args"]) in
  let spec_sspecs=read_list r read_single (route@["spec_sspecs"]) in
  let spec_normalised=rb r (route@["spec_normalised"]) in
  let spec_incomplete=rb r (route@["spec_incomplete"]) in
  let spec_to_verify=rb r (route@["spec_to_verify"]) in
  let spec_location=read_option r rl (route@["spec_location"]) in
  {spec_name;spec_params;spec_raw_args;spec_sspecs;spec_normalised;spec_incomplete;spec_to_verify;spec_location}
let write_pred w route (p:TypeDef__.pred) =
  ws w (route@["pred_name"]) p.pred_name;
  write_option w ws (route@["pred_source_path"]) p.pred_source_path;
  write_option w wl (route@["pred_loc"]) p.pred_loc;
  wb w (route@["pred_internal"]) p.pred_internal;
  wi w (route@["pred_num_params"]) p.pred_num_params;
  write_list w write_param (route@["pred_params"]) p.pred_params;
  wi w (route@["ins_number"]) p.ins_number;
  write_list w write_definition (route@["pred_definitions"]) p.pred_definitions;
  write_list w we (route@["pred_facts"]) p.pred_facts;
  write_option w write_assertion (route@["pred_guard"]) p.pred_guard;
  wb w (route@["pred_pure"]) p.pred_pure;wb w (route@["pred_abstract"]) p.pred_abstract;
  wb w (route@["pred_nounfold"]) p.pred_nounfold;wb w (route@["pred_normalised"]) p.pred_normalised
let read_pred r route : TypeDef__.pred =
  let pred_name=rs r (route@["pred_name"]) in
  let pred_source_path=read_option r rs (route@["pred_source_path"]) in
  let pred_loc=read_option r rl (route@["pred_loc"]) in
  let pred_internal=rb r (route@["pred_internal"]) in
  let pred_num_params=ri r (route@["pred_num_params"]) in
  let pred_params=read_list r read_param (route@["pred_params"]) in
  let ins_number=ri r (route@["ins_number"]) in
  let pred_definitions=read_list r read_definition (route@["pred_definitions"]) in
  let pred_facts=read_list r re (route@["pred_facts"]) in
  let pred_guard=read_option r read_assertion (route@["pred_guard"]) in
  let pred_pure=rb r (route@["pred_pure"]) in
  let pred_abstract=rb r (route@["pred_abstract"]) in
  let pred_nounfold=rb r (route@["pred_nounfold"]) in
  let pred_normalised=rb r (route@["pred_normalised"]) in
  {pred_name;pred_source_path;pred_loc;pred_internal;pred_num_params;pred_params;
   ins_number;pred_definitions;pred_facts;pred_guard;pred_pure;pred_abstract;
   pred_nounfold;pred_normalised}
let emit_parent kind write emit route value =
  at route (fun () ->
    let found=K.inspect_parent_v4 value in
    let w={emit;allowed=ref []} in
    emit "fragment-open" route (K.checked_v4 ~to_json:jstring ~of_json:string_of kind);
    write w route value;
    K.check_parent_customs_v4 found !(w.allowed);
    emit "fragment-close" route (K.checked_v4 ~to_json:jstring ~of_json:string_of kind))
let read_parent kind read take route =
  at route (fun () ->
    require (take "fragment-open" route=`String kind) "fragment parent kind";
    let r={take;allowed=ref []} in
    let value=read r route in
    require (take "fragment-close" route=`String kind) "fragment parent closure";
    K.check_parent_customs_v4 (K.inspect_parent_v4 value) !(r.allowed);
    value)
let emit_pred ~emit ~route value = emit_parent "pred" write_pred emit route value
let take_pred ~take ~route = read_parent "pred" read_pred take route
let emit_spec ~emit ~route value = emit_parent "spec" write_spec emit route value
let take_spec ~take ~route = read_parent "spec" read_spec take route
let emit_optional_spec ~emit ~route value =
  emit_parent "optional-spec" (fun w route -> write_option w write_spec route) emit route value
let take_optional_spec ~take ~route =
  read_parent "optional-spec" (fun r route -> read_option r read_spec route) take route
