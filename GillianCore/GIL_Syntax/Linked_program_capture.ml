(* Passive snapshots. Decoded values are checked then discarded, never verified. *)
module Codec = Linked_capture_codec
module Writer = Linked_capture_writer
module Fragments = Linked_capture_fragments
let fail why = raise (Codec.Incomplete why)
let require = Codec.require
let policy version =
  require(version=1 || version=2 || version=3 || version=4 || version=5)"capture version";
  if version=1 then "linked-program-capture-v1"
  else if version=2 then "linked-program-capture-single-frame-v2"
  else if version=3 then "linked-program-capture-bounded-v3"
  else if version=4 then "linked-program-capture-fragmented-v4"
  else "linked-program-capture-compact-routes-v5"
let version_of_policy = function
  |None|Some "linked-program-capture-v1"->1
  |Some "linked-program-capture-single-frame-v2"->2
  |Some "linked-program-capture-bounded-v3"->3
  |Some "linked-program-capture-fragmented-v4"->4
  |Some "linked-program-capture-compact-routes-v5"->5
  |Some _->fail "unknown linked program capture policy"
let jstring s = `String s
let string_of_json = function `String s->Ok s |_->Error "string"
let jint n = `Int n
let int_of_json = function `Int n->Ok n |_->Error "int"
let jbool b = `Bool b
let bool_of_json = function `Bool b->Ok b |_->Error "bool"
let option to_json = function None->`Null |Some value->to_json value
let option_of from_json = function
  | `Null->Ok None |value->Result.map (fun x->Some x) (from_json value)
let jlist to_json xs = `List(List.map to_json xs)
let list_of from_json = function
  | `List xs ->
      let rec loop acc = function []->Ok(List.rev acc) |x::xs->
        (match from_json x with Error e->Error e |Ok x->loop(x::acc)xs) in
      loop [] xs
  |_->Error "list"
let pair to_a to_b (a,b) = `List[to_a a;to_b b]
let pair_of of_a of_b = function
  | `List[a;b] -> (match of_a a,of_b b with Ok a,Ok b->Ok(a,b) |Error e,_|_,Error e->Error e)
  |_->Error "pair"
let checked ?(version=1) ?guard to_json of_json value =
  if version=4 || version=5 then Codec.checked_v4 ?guard ~to_json ~of_json value
  else Codec.checked ~version ?guard ~to_json ~of_json value
let ast ?(version=1) visit to_json of_json value =
  let guard = if version>=3 then Codec.guard_ast_v3 visit else Codec.guard_ast visit in
  checked ~version ~guard to_json of_json value
let proc_fields = ["proc_name";"proc_source_path";"proc_internal";"proc_body";
                   "proc_params";"proc_spec";"proc_aliases";"proc_calls";
                   "proc_display_name";"proc_hidden"]
type frame = {phase:string;seq:int;kind:string;route:string list;payload:Yojson.Safe.t}
let logical_frame_json ?(version=1) f =
  ignore(policy version);
  let json=`Assoc[
    "schema",`Int version;"phase",`String f.phase;"sequence",`Int f.seq;
    "kind",`String f.kind;"route",`List(List.map(fun s->`String(Codec.hex s))f.route);
    "payload",f.payload] in
  if version>=3 then Codec.guard_transport_v3 json
  else if version=2 then Codec.guard_transport json;
  json
let frame_json ?(version=1) f =
  require(version<>5)"V5 requires stateful route transport";
  logical_frame_json ~version f
let frame_of_json ?(version=1) json =
  require(version<>5)"V5 requires stateful route transport";
  ignore(policy version);
  (if version>=3 then Codec.guard_transport_v3 else Codec.guard_transport) json;match json with
  | `Assoc["schema",`Int schema;"phase",`String phase;"sequence",`Int seq;
           "kind",`String kind;"route",`List route;"payload",payload] when schema=version ->
      let route=List.map(function `String s->Codec.unhex s |_->fail "route bytes")route in
      {phase;seq;kind;route;payload}
  |_->fail "frame exact schema/order"

(* V5 changes only wire metadata. Every accepted expanded logical frame keeps
   the old full-envelope guard and complete-line cap as well as the wire cap. *)
module V5_route = struct
  type state={phase:string;mutable previous:string list;mutable next:int;mutable failed:bool}
  type encoder=Encoder of state
  type decoder=Decoder of state
  let create phase =
    require(phase="linked"||phase="post-logic")"V5 route phase";
    {phase;previous=[];next=0;failed=false}
  let encoder ~phase=Encoder(create phase)
  let decoder ~phase=Decoder(create phase)
  let operation state f =
    try require(not state.failed)"V5 route state poisoned";f ()
    with e->state.failed<-true;raise e
  let guard_line json =
    Codec.guard_transport_v3 json;
    require(String.length(Yojson.Safe.to_string json)+1<=Codec.fragment_bytes)
      "capture frame1MiB cap"
  let common a b =
    let rec loop n a b=match a,b with
      |x::xs,y::ys when String.equal x y->loop(n+1)xs ys
      |_->n in loop 0 a b
  let drop n xs =
    let rec loop n xs=if n=0 then xs else match xs with
      |_::rest->loop(n-1)rest|[]->fail "V5 route prefix" in loop n xs
  let prefix n xs =
    let rec loop n xs acc=if n=0 then List.rev acc else match xs with
      |x::rest->loop(n-1)rest(x::acc)|[]->fail "V5 route prefix" in loop n xs []
  let absolute route=`List(List.map(fun s->`String(Codec.hex s))route)
  let route_code previous route =
    let keep=common previous route in
    let absolute=absolute route and suffix=absolute(drop keep route) in
    let delta=`List[`Int keep;suffix] in
    if String.length(Yojson.Safe.to_string delta)<String.length(Yojson.Safe.to_string absolute)
    then delta else absolute
  let check_frame state (frame:frame) =
    require(frame.phase=state.phase)"V5 route phase";
    require(frame.seq=state.next)"V5 route sequence"
  let commit state (frame:frame) =
    state.previous<-frame.route;state.next<-state.next+1
  let encode (Encoder state) frame = operation state(fun()->
    check_frame state frame;
    guard_line(logical_frame_json ~version:5 frame);
    let json=`List[`Int 5;`String frame.phase;`Int frame.seq;`String frame.kind;
      route_code state.previous frame.route;frame.payload] in
    guard_line json;commit state frame;json)
  let decode (Decoder state) json = operation state(fun()->
    guard_line json;
    match json with
    |`List[`Int 5;`String phase;`Int seq;`String kind;code;payload]->
        let strings xs=List.map(function `String s->Codec.unhex s
          |_->fail "V5 route code")xs in
        let route=match code with
          |`List[`Int keep;`List suffix]->
              require(keep>=0&&keep<=List.length state.previous)"V5 route prefix";
              prefix keep state.previous @ strings suffix
          |`List xs->strings xs
          |_->fail "V5 route code" in
        require(Codec.equal code(route_code state.previous route))"V5 noncanonical route code";
        let frame={phase;seq;kind;route;payload} in
        check_frame state frame;
        guard_line(logical_frame_json ~version:5 frame);
        commit state frame;frame
    |_->fail "V5 compact tuple schema")
end
let tables = ["lemmas";"preds";"funcs";"datatypes";"only_specs";"procs";"macros";"bi_specs"]
let bounded_length limit values =
  let rec count n = function []->n | _::rest->require(n<limit)"list inventory budget/cycle";count(n+1)rest in
  count 0 values
let inventory table =
  let n=Hashtbl.length table in require(n>=0&&n<=32768)"table inventory budget";
  let keys=Hashtbl.fold(fun k _ acc->k::acc)table[] |> List.sort_uniq String.compare in
  List.iter Codec.guard_plain keys;
  let bindings=List.map(fun key->key,Hashtbl.find_all table key)keys in
  require(List.fold_left(fun n(_,values)->n+List.length values)0 bindings=n)"complete table binding inventory";bindings
let iter_program ?(version=1) ~annot_to_json ~annot_of_json ~phase ~emit (prog:('a,int) Prog.t) =
  let policy=policy version in
  require(phase="linked" || phase="post-logic")"capture phase";
  let seq=ref 0 in
  let output kind route payload =
    let frame={phase;seq= !seq;kind;route;payload} in incr seq;emit frame
  in
  let plain to_json from value = checked ~version to_json from value in
  output "header" [] (plain (jlist jstring) (list_of string_of_json)
    [policy;Sys.ocaml_version;string_of_int Sys.word_size;string_of_bool Sys.big_endian]);
  let list name to_json from values =
    let n=bounded_length 32768 values in
    output "list" [name] (plain jint int_of_json n);
    List.iteri(fun i value->output "item" [name;string_of_int i] (plain to_json from value))values
  in
  list "imports" (pair jstring jbool) (pair_of string_of_json bool_of_json) prog.imports;
  let table name tbl encode =
    let bindings=inventory tbl in
    let header_to (keys,values)=`List[`Int keys;`Int values;`String "sorted-unique-keys/find_all-latest-first"] in
    let header_of=function `List[`Int k;`Int v;`String "sorted-unique-keys/find_all-latest-first"]->Ok(k,v)|_->Error "table binding header" in
    output "table" [name] (plain header_to header_of (List.length bindings,Hashtbl.length tbl));
    List.iteri(fun i (key,values)->
      let route=[name;string_of_int i;key] in
      output "key" route (plain (pair jstring jint) (pair_of string_of_json int_of_json) (key,List.length values));
      List.iteri(fun ordinal value->
        try encode (route@[string_of_int ordinal]) value with
        | Codec.Incomplete why ->
            let prefix=String.sub key 0 (min 32 (String.length key)) in
            raise(Codec.Incomplete(Printf.sprintf
              "%s phase=%s table=%s keyIndex=%d keyHexPrefix=%s bindingOrdinal=%d"
              why phase name i (Codec.hex prefix) ordinal)))values)bindings
  in
  let entry visit to_json from route value = output "value" route (ast ~version visit to_json from value) in
  table "lemmas" prog.lemmas (entry(fun v x->v#visit_lemma () x) TypeDef__.lemma_to_yojson TypeDef__.lemma_of_yojson);
  table "preds" prog.preds (if version=4 || version=5 then
    (fun route value->Fragments.emit_pred ~emit:output ~route value)
    else entry(fun v x->v#visit_pred () x) TypeDef__.pred_to_yojson TypeDef__.pred_of_yojson);
  table "funcs" prog.funcs (entry(fun v x->v#visit_func () x) TypeDef__.func_to_yojson TypeDef__.func_of_yojson);
  table "datatypes" prog.datatypes (entry(fun v x->v#visit_datatype () x) TypeDef__.datatype_to_yojson TypeDef__.datatype_of_yojson);
  table "only_specs" prog.only_specs (if version=4 || version=5 then
    (fun route value->Fragments.emit_spec ~emit:output ~route value)
    else entry(fun v x->v#visit_spec () x) TypeDef__.spec_to_yojson TypeDef__.spec_of_yojson);
  table "procs" prog.procs (fun route (p:('a,int) Proc.t)->
      let field name payload=output "proc-field" (route@[name]) payload in
      field "proc_name" (plain jstring string_of_json p.proc_name);
      field "proc_source_path" (plain (option jstring) (option_of string_of_json) p.proc_source_path);
      field "proc_internal" (plain jbool bool_of_json p.proc_internal);
      require(Array.length p.proc_body<=262144)"procedure command count budget";
      field "proc_body" (plain jint int_of_json (Array.length p.proc_body));
      let triple_to_json (a,label,cmd)=`List[annot_to_json a;option jint label;TypeDef__.cmd_to_yojson jint cmd] in
      let triple_of_json=function
        |`List[a;label;cmd]->(match annot_of_json a,option_of int_of_json label,TypeDef__.cmd_of_yojson int_of_json cmd with
          |Ok a,Ok label,Ok cmd->Ok(a,label,cmd)
          |Error e,_,_|_,Error e,_|_,_,Error e->Error e)
        |_->Error "body triple" in
      Array.iteri(fun i ((_,_,cmd)as triple)->
          let guard value=(if version>=3 then Codec.guard_ast_v3 else Codec.guard_ast)
            (fun v (_,_,c)->v#visit_cmd () c) value in
          ignore cmd;
          output "command" (route@["proc_body";string_of_int i])
            (checked ~version ~guard triple_to_json triple_of_json triple))p.proc_body;
      field "proc_params" (plain (jlist jstring) (list_of string_of_json) p.proc_params);
      (if version=4 || version=5 then Fragments.emit_optional_spec ~emit:output ~route:(route@["proc_spec"]) p.proc_spec
      else field "proc_spec" (ast ~version (fun v x->Option.iter(v#visit_spec ())x)
        (option TypeDef__.spec_to_yojson) (option_of TypeDef__.spec_of_yojson) p.proc_spec));
      field "proc_aliases" (plain (jlist jstring) (list_of string_of_json) p.proc_aliases);
      field "proc_calls" (plain (jlist jstring) (list_of string_of_json) p.proc_calls);
      field "proc_display_name" (plain (option(pair jstring jstring))
        (option_of(pair_of string_of_json string_of_json)) p.proc_display_name);
      field "proc_hidden" (plain jbool bool_of_json p.proc_hidden));
  table "macros" prog.macros (entry(fun v x->v#visit_macro () x) TypeDef__.macro_to_yojson TypeDef__.macro_of_yojson);
  table "bi_specs" prog.bi_specs (entry(fun v x->v#visit_bispec () x) TypeDef__.bispec_to_yojson TypeDef__.bispec_of_yojson);
  list "proc_names" jstring string_of_json prog.proc_names;
  require(Hashtbl.length prog.predecessors<=262144)"predecessor count budget";
  let predecessor_keys=Hashtbl.fold(fun key _ acc->key::acc)prog.predecessors[] |> List.sort_uniq compare in
  let predecessors=List.concat_map(fun(name,j,i)->List.mapi(fun ordinal k->(name,j,i,k),ordinal)
    (Hashtbl.find_all prog.predecessors (name,j,i)))predecessor_keys in
  require(List.length predecessors=Hashtbl.length prog.predecessors)"complete predecessor bindings";
  let pred_header_to n=`List[`Int n;`String "sorted-key/find_all-latest-first"] in
  let pred_header_of=function `List[`Int n;`String "sorted-key/find_all-latest-first"]->Ok n|_->Error "predecessor binding convention" in
  output "list" ["predecessors"] (plain pred_header_to pred_header_of (List.length predecessors));
  let pred_to (name,j,i,k)=`List[`String name;`Int j;`Int i;`Int k] in
  let pred_of=function `List[`String n;`Int j;`Int i;`Int k]->Ok(n,j,i,k)|_->Error "predecessor tuple" in
  List.iteri(fun i (row,ordinal)->output "item" ["predecessors";string_of_int i;string_of_int ordinal] (plain pred_to pred_of row))predecessors;
  output "footer" [] (plain jint int_of_json !seq)

(* A finite reader grammar: no missing/duplicate/renumbered/reordered/wrong-kind
   frame can count as a complete stream. It does not assert theorem fidelity. *)
let validate_frames ?(version=1) frames =
  let policy=policy version in
  let transport_guard=if version>=3 then Codec.guard_transport_v3 else Codec.guard_transport in
  let remaining=ref frames and at=ref 0 and phase=ref None in
  let take kind route = match !remaining with
    |f::rest->require(f.seq= !at && f.kind=kind && f.route=route)"frame order/kind/route";
       (match !phase with None->require(f.phase="linked"||f.phase="post-logic")"frame phase";phase:=Some f.phase
        |Some p->require(p=f.phase)"mixed phase");
       incr at;remaining:=rest;transport_guard f.payload;Codec.untag f.payload
    |[]->fail "missing frame" in
  let count kind route=match take kind route with `Int n when n>=0&&n<=262144->n|_->fail "inventory count" in
  (match take "header" [] with `List[`String format;`String _;`String _;`String _] when format=policy->()|_->fail "header ABI");
  let list name=let n=count "list" [name] in for i=0 to n-1 do ignore(take "item" [name;string_of_int i])done in
  list "imports";
  List.iter(fun table->
      let n,total=match take "table" [table] with
        |`List[`Int n;`Int total;`String "sorted-unique-keys/find_all-latest-first"] when n>=0&&total>=n&&total<=32768->n,total
        |_->fail "table binding counts/convention" in
      let previous=ref None and seen=ref 0 in
      for i=0 to n-1 do
        let key=match !remaining with f::_->(match f.route with [t;j;k] when t=table&&j=string_of_int i->k|_->fail "key route")|_->fail "missing key" in
        (match !previous with None->()|Some p->require(String.compare p key<0)"sorted unique key inventory");previous:=Some key;
        let key_route=[table;string_of_int i;key] in
        let bindings=match take "key" key_route with
          |`List[`String name;`Int n] when name=key&&n>0&&n<=32768->n|_->fail "key binding count" in
        seen:= !seen+bindings;require(!seen<=total)"binding total overflow";
        for ordinal=0 to bindings-1 do
          let route=key_route@[string_of_int ordinal] in
          if (version=4 || version=5) && table="preds" then ignore(Fragments.take_pred ~take ~route)
          else if (version=4 || version=5) && table="only_specs" then ignore(Fragments.take_spec ~take ~route)
          else if table<>"procs" then ignore(take "value" route)
          else List.iter(fun field->
            if field="proc_body" then (
              let n=count "proc-field" (route@[field]) in
              for j=0 to n-1 do ignore(take "command" (route@[field;string_of_int j]))done)
            else if (version=4 || version=5) && field="proc_spec" then
              ignore(Fragments.take_optional_spec ~take ~route:(route@[field]))
            else ignore(take "proc-field" (route@[field])))proc_fields
        done
      done;require(!seen=total)"all table bindings required")tables;
  list "proc_names";
  let n=match take "list" ["predecessors"] with
    |`List[`Int n;`String "sorted-key/find_all-latest-first"] when n>=0&&n<=262144->n
    |_->fail "predecessor count/convention" in
  let previous=ref None and ordinal=ref 0 in
  for i=0 to n-1 do
    let key,actual=match !remaining with
      |f::_->transport_guard f.payload;(match Codec.untag f.payload with `List[`String p;`Int j;`Int k;`Int _]->(p,j,k),f.route|_->fail "raw predecessor tuple")
      |_->fail "missing predecessor" in
    (match !previous with None->ordinal:=0 |Some p->
      let c=compare p key in require(c<=0)"sorted predecessor keys";if c=0 then incr ordinal else ordinal:=0);
    require(actual=["predecessors";string_of_int i;string_of_int !ordinal])"predecessor binding ordinal";
    ignore(take "item" actual);previous:=Some key
  done;
  let expected= !at in require(take "footer" []=`Int expected)"footer frame count";
  require(!remaining=[])"extra frames"

type session={writer:Writer.t;version:int;mutable next:int;mutable counts:int list}
let operation f = try f() with
  |Gillian_result.Exc.Gillian_error _ as e->raise e
  |e->raise(Gillian_result.Exc.Gillian_error(Gillian_result.Error.OperationError
      ("Linked program capture incomplete: " ^ Printexc.to_string e)))
let with_session f =
  let version=operation(fun()->version_of_policy(Sys.getenv_opt "GILLIAN_LINKED_PROGRAM_CAPTURE_POLICY")) in
  match Sys.getenv_opt "GILLIAN_LINKED_PROGRAM_CAPTURE_DIR" with
  |None->f None (* No traversal, conversion or IO in the disabled path. *)
  |Some root->
      let writer=operation(fun()->Writer.create root) in
      let session={writer;version;next=0;counts=[]} in
      try
        let result=f(Some session) in
        operation(fun()->require(session.next=2)"both synchronous program snapshots required");result
      with e->Writer.abort session.writer "capture or verifier exited before normal closure";raise e
let capture session ~annot_to_json ~annot_of_json ~phase prog = match session with
  |None->()
  |Some session->operation(fun()->
      require((session.next=0&&phase="linked")||(session.next=1&&phase="post-logic"))"snapshot invocation order";
      Writer.start session.writer session.next;
      let count=ref 0 in
      let encoder=if session.version=5 then Some(V5_route.encoder ~phase) else None in
      (* V4/V5 batch only complete, individually guarded JSONL frames. Durability
         is at each Writer.write batch and phase closure, not per-frame fsync.
         Writer retains every prospective/encoded/identity/close check. A failed
         write leaves its buffer uncleared and cannot advance the phase. *)
      let pending=if session.version=4 || session.version=5 then Some(Buffer.create Codec.fragment_bytes) else None in
      let flush ()=match pending with
        |Some buffer when Buffer.length buffer>0->
            Writer.write session.writer(Buffer.contents buffer);Buffer.clear buffer
        |_->() in
      let write text=match pending with
        |None->Writer.write session.writer text
        |Some buffer->
            let n=String.length text in
            require(n<=Codec.fragment_bytes)"capture frame1MiB cap";
            if Buffer.length buffer>Codec.fragment_bytes-n then flush();
            Buffer.add_string buffer text in
      iter_program ~version:session.version ~annot_to_json ~annot_of_json ~phase ~emit:(fun frame->
          incr count;
          let json=match encoder with Some encoder->V5_route.encode encoder frame
            |None->frame_json ~version:session.version frame in
          let text=Yojson.Safe.to_string json^"\n" in write text)prog;
      flush();
      Writer.close_phase session.writer;session.next<-session.next+1;session.counts<-session.counts@[!count];
      if session.next=2 then (
        let manifest=`Assoc(("schema",`Int session.version)::
          ((if session.version=1 then [] else ["codecPolicy",`String(policy session.version)])@
          ["phaseFiles",`List[`String "00000000.jsonl";`String "00000001.jsonl"];
           "frameCounts",`List(List.map(fun n->`Int n)session.counts);"requiresNativeSuccessAndClosedWriter",`Bool true;
           "proofAccepted",`Bool false])) in
        if session.version>=3 then Codec.guard_transport_v3 manifest
        else if session.version=2 then Codec.guard_transport manifest;
        Writer.finish session.writer (Yojson.Safe.to_string manifest^"\n")))
