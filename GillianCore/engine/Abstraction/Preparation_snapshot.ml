(* V4 capture representation only. Source-bound typed/state guards remain in
   Preparation_provenance/Verifier. Packed tables and one bounded byte store
   retain encoded values, never mutable native states or expanded tagged trees. *)
module C = Linked_program_capture.Codec
module F = Preparation_framing
let require = C.require
let byte_cap = 16 * 1024 * 1024
let max_ids = byte_cap / 31
let stride = 256
let slots = 2097152 (*16B/slot <64B/max_ids, load <=0.259; no boxed ID table. *)
let node_cap = 262144
let string_cap = 1048576

(* SHA256 has no library/process dependency. It supplies payload integrity only;
   external complete-ledger SHA256/native custody remain the root authority. *)
module Hash = struct
  let k = Array.map Int32.of_string [|
    "0x428a2f98";"0x71374491";"0xb5c0fbcf";"0xe9b5dba5";"0x3956c25b";"0x59f111f1";"0x923f82a4";"0xab1c5ed5";
    "0xd807aa98";"0x12835b01";"0x243185be";"0x550c7dc3";"0x72be5d74";"0x80deb1fe";"0x9bdc06a7";"0xc19bf174";
    "0xe49b69c1";"0xefbe4786";"0x0fc19dc6";"0x240ca1cc";"0x2de92c6f";"0x4a7484aa";"0x5cb0a9dc";"0x76f988da";
    "0x983e5152";"0xa831c66d";"0xb00327c8";"0xbf597fc7";"0xc6e00bf3";"0xd5a79147";"0x06ca6351";"0x14292967";
    "0x27b70a85";"0x2e1b2138";"0x4d2c6dfc";"0x53380d13";"0x650a7354";"0x766a0abb";"0x81c2c92e";"0x92722c85";
    "0xa2bfe8a1";"0xa81a664b";"0xc24b8b70";"0xc76c51a3";"0xd192e819";"0xd6990624";"0xf40e3585";"0x106aa070";
    "0x19a4c116";"0x1e376c08";"0x2748774c";"0x34b0bcb5";"0x391c0cb3";"0x4ed8aa4a";"0x5b9cca4f";"0x682e6ff3";
    "0x748f82ee";"0x78a5636f";"0x84c87814";"0x8cc70208";"0x90befffa";"0xa4506ceb";"0xbef9a3f7";"0xc67178f2"|]
  type t = { h:int32 array; block:bytes; mutable used:int; mutable length:int64 }
  let create () = {h=Array.map Int32.of_string [|"0x6a09e667";"0xbb67ae85";"0x3c6ef372";"0xa54ff53a";"0x510e527f";"0x9b05688c";"0x1f83d9ab";"0x5be0cd19"|];block=Bytes.create 64;used=0;length=0L}
  let r x n = Int32.logor (Int32.shift_right_logical x n) (Int32.shift_left x (32-n))
  let xor3 a b c = Int32.logxor a (Int32.logxor b c)
  let add = Int32.add
  let compress t =
    let w=Array.make 64 0l in
    for i=0 to 15 do w.(i)<-Bytes.get_int32_be t.block (4*i) done;
    for i=16 to 63 do
      let x=w.(i-15) and y=w.(i-2) in
      let a=xor3 (r x 7) (r x 18) (Int32.shift_right_logical x 3) in
      let b=xor3 (r y 17) (r y 19) (Int32.shift_right_logical y 10) in
      w.(i)<-add (add w.(i-16) a) (add w.(i-7) b)
    done;
    let a=ref t.h.(0) and b=ref t.h.(1) and c=ref t.h.(2) and d=ref t.h.(3)
      and e=ref t.h.(4) and f=ref t.h.(5) and g=ref t.h.(6) and h=ref t.h.(7) in
    for i=0 to 63 do
      let s=xor3 (r !e 6) (r !e 11) (r !e 25) in
      let ch=Int32.logxor (Int32.logand !e !f) (Int32.logand (Int32.lognot !e) !g) in
      let p=add (add (add !h s) ch) (add k.(i) w.(i)) in
      let s=xor3 (r !a 2) (r !a 13) (r !a 22) in
      let maj=xor3 (Int32.logand !a !b) (Int32.logand !a !c) (Int32.logand !b !c) in
      h:= !g;g:= !f;f:= !e;e:=add !d p;d:= !c;c:= !b;b:= !a;a:=add p (add s maj)
    done;
    Array.iteri (fun i x -> t.h.(i)<-add t.h.(i) x) [|!a;!b;!c;!d;!e;!f;!g;!h|]
  let update t s =
    t.length<-Int64.add t.length (Int64.of_int (String.length s));
    let at=ref 0 in while !at<String.length s do
      let n=min (64-t.used) (String.length s- !at) in
      Bytes.blit_string s !at t.block t.used n;t.used<-t.used+n;at:= !at+n;
      if t.used=64 then (compress t;t.used<-0)
    done
  let finish t =
    let bits=Int64.mul t.length 8L in
    update t "\128";
    while t.used<>56 do update t "\000" done;
    let tail=Bytes.create 8 in Bytes.set_int64_be tail 0 bits;update t (Bytes.to_string tail);
    String.concat "" (Array.to_list (Array.map (Printf.sprintf "%08lx") t.h))
  let text s = let t=create () in update t s;finish t
end

type stats = { rw:int;tw:int;rs:int;ts:int;n:int;d:int;j:int;jd:int;b:int }
let zero = {rw=0;tw=0;rs=0;ts=0;n=0;d=0;j=0;jd=0;b=0}
let limit = 16 * byte_cap (*saturation only; all real admissions are below. *)
let plus a b = if a>limit-b then limit else a+b
let sum f xs = List.fold_left (fun n x -> plus n (f x)) 0 xs
let sw n = 1+(n+8)/8
let header name arity = 6+3*arity+sw(String.length name)
let quote s = Yojson.Safe.to_string (`String s)
let scalar_stats ?encoded json =
  let tag,rw,rs,extra,ts = match json with
    | `Null -> "null",0,0,0,0
    | `Bool _ -> "bool",3,0,3,0
    | `Int n -> let s=string_of_int n in "int",3,0,3+sw(String.length s),String.length s
    | `Float _ -> "float64",5,0,3+sw 16,16
    | `String s -> require(String.length s<=262144)"v4-scalar-string";
        "bytes",3+sw(String.length s),String.length s,3+sw(2*String.length s),2*String.length s
    | `Intlit s -> require(String.length s<=262144)"v4-scalar-string";
        "intlit",3+sw(String.length s),String.length s,3+sw(2*String.length s),2*String.length s
    | `Variant(name,None) -> require(String.length name<=262144)"v4-scalar-name";
        "variant-none",6+sw(String.length name),String.length name,3+sw(2*String.length name),2*String.length name
    | _ -> raise(C.Incomplete "v4-not-scalar") in
  let encoded=match encoded with Some text->text|None->Yojson.Safe.to_string(C.tag json)in
  {rw;tw=header tag (if tag="null"then 1 else 2)+extra;rs;
   ts=String.length tag+ts;n=1;d=0;j=(if tag="null"then 2 else 3);jd=1;b=String.length encoded}
let container_stats kind name entries =
  let children=List.map snd entries in
  let count=List.length entries in
  let maxd f = List.fold_left(fun n x -> max n (f x))0 children in
  let rw,rs,tw,ts,j,b,d,jd = if kind="assoc" then (
    let keys=List.map fst entries in
    3+6*count+sum(fun k -> sw(String.length k))keys+sum(fun x->x.rw)children,
    sum String.length keys+sum(fun x->x.rs)children,
    header kind 2+3+15*count+sum(fun k->sw(2*String.length k))keys+sum(fun x->x.tw)children,
    String.length kind+sum(fun k->2*String.length k)keys+sum(fun x->x.ts)children,
    3+2*count+sum(fun x->x.j)children,
    String.length("[\""^kind^"\",[")+2+max 0(count-1)+sum(fun(k,x)->5+2*String.length k+x.b)entries,
    (if count=0 then 0 else 1+maxd(fun x->x.d)),(if count=0 then 1 else 3+maxd(fun x->x.jd)))
  else if kind="variant-some" then (
    require(count=1)"v4-variant-arity";let x=List.hd children in
    8+sw(String.length name)+x.rw,String.length name+x.rs,
    header kind 3+3+sw(2*String.length name)+x.tw,String.length kind+2*String.length name+x.ts,
    3+x.j,String.length("[\"variant-some\",\""^C.hex name^"\",")+1+x.b,1+x.d,max 1 (1+x.jd))
  else (
    3+3*count+sum(fun x->x.rw)children,sum(fun x->x.rs)children,
    header kind 2+3+3*count+sum(fun x->x.tw)children,String.length kind+sum(fun x->x.ts)children,
    3+sum(fun x->x.j)children,String.length("[\""^kind^"\",[")+2+max 0(count-1)+sum(fun x->x.b)children,
    (if count=0 then 0 else 1+maxd(fun x->x.d)),(if count=0 then 1 else 2+maxd(fun x->x.jd))) in
  {rw;tw;rs;ts;n=1+sum(fun x->x.n)children;d;j;jd;b}

type imported = { sequence:int;role:string;offset:int;bytes:int;stats:stats }
type t = { mutable store:bytes;mutable desc:bytes;mutable index:bytes;mutable used:int;mutable next:int;
  mutable visible:int;mutable committed_sequence:int;mutable opened:bool;
  mutable scratch:bytes;mutable scratch_used:int;keep_observations:bool;
  imports:(string,imported)Hashtbl.t;mutable observations:Yojson.Safe.t list;mutable pending:Yojson.Safe.t option }
let create ?(observations=false) () = {keep_observations=observations;store=Bytes.create byte_cap;desc=Bytes.create(max_ids*stride);
 index=Bytes.create(slots*16);scratch=Bytes.create byte_cap;scratch_used=0;used=0;next=0;visible=0;committed_sequence=(-1);opened=false;
 imports=Hashtbl.create 31;observations=[];pending=None}
let release t = t.store<-Bytes.empty;t.desc<-Bytes.empty;t.index<-Bytes.empty;t.scratch<-Bytes.empty;t.scratch_used<-0;
 Hashtbl.clear t.imports;t.pending<-None;t.opened<-false
let position t=t.used
let append t s = require(String.length s<=byte_cap-t.used)"v4-global-decoded-store";
  Bytes.blit_string s 0 t.store t.used(String.length s);t.used<-t.used+String.length s
let di t id off = Int32.to_int(Bytes.get_int32_le t.desc(id*stride+off))
let seti t id off n=Bytes.set_int32_le t.desc(id*stride+off)(Int32.of_int n)
let setstats t id x = Array.iteri(fun i n->Bytes.set_int64_le t.desc(id*stride+64+8*i)(Int64.of_int n))
 [|x.rw;x.tw;x.rs;x.ts;x.n;x.d;x.j;x.jd;x.b|]
let stats t id =
  let x i=Int64.to_int(Bytes.get_int64_le t.desc(id*stride+64+8*i))in
  {rw=x 0;tw=x 1;rs=x 2;ts=x 3;n=x 4;d=x 5;j=x 6;jd=x 7;b=x 8}
let id n=Printf.sprintf "%08x"n
let idj n=`String(id n)
let from_id = function `String s when String.length s=8 -> int_of_string("0x"^s)
 | _->raise(C.Incomplete "v4-private-id")
let key t n=Bytes.sub_string t.store(di t n 4)(di t n 8)
let same_key t n text =
 let offset=di t n 4 and len=di t n 8 in
 len=String.length text && (let rec go i=i=len||(Bytes.get t.store(offset+i)=text.[i]&&go(i+1))in go 0)
let hash=F.checksum_update F.checksum_initial
let lookup t code text =
 let h=F.checksum_update (hash(string_of_int code)) text in let first=Int64.to_int(Int64.logand h(Int64.of_int(slots-1)))in
 let found=ref None and vacant=ref None and stop=ref false in
 (*64 probes bound collision work. Failure to intern is a duplicate definition,
   never a false equality or a change to the resolved value/admission guard. *)
 for k=0 to 63 do if not !stop then (
  let slot=((first+k)land(slots-1))*16 in
  let n=Int32.to_int(Bytes.get_int32_le t.index(slot+8))in
  if n=0 then(vacant:=Some slot;stop:=true)
  else if Bytes.get_int64_le t.index slot=h&&di t(n-1)0=code&&same_key t(n-1)text
  then(found:=Some(n-1);stop:=true))done;
 h,!found,!vacant
let define t ~put ~op ~key_text ~code ~st ~attrs =
 let h,found,vacant=lookup t code key_text in match found with Some n->n |None ->
 require(t.next<max_ids)"v4-global-definition-count";
 let n=t.next in let prefix="[\""^op^"\",\""^id n^"\","in
 let offset=t.used+String.length prefix in
 require(String.length prefix+String.length key_text+2<=1048576)"v4-definition-line";
 put prefix;put key_text;put "]\n";
 seti t n 0 code;seti t n 4 offset;seti t n 8(String.length key_text);
 List.iter(fun(off,value)->seti t n off value)attrs;setstats t n st;t.next<-n+1;
 Option.iter(fun slot->Bytes.set_int64_le t.index slot h;Bytes.set_int32_le t.index(slot+8)(Int32.of_int(n+1)))vacant;n
let origin_key ~source ~parent ~alternative ~expanded =
 require(source>=0&&source<=4096&&parent>=0&&parent<=4096&&alternative>=0&&alternative<=4096&&expanded>=0&&expanded<=4096)
  "v4-private-origin-key";
 Printf.sprintf "%d:%d:%d:%d" source parent alternative expanded
let commit t ~sequence = require(sequence=t.committed_sequence+1)"v4-commit-sequence";
 require(not t.opened||Option.is_some t.pending)"v4-commit-before-snapshot-end";
 t.opened<-false;
 t.committed_sequence<-sequence;t.visible<-t.next;
 (match t.pending with None->()|Some row->if t.keep_observations then t.observations<-row::t.observations;t.pending<-None)

(* Fold one already source-guarded derived field. Work is occurrence-based;
   repeated JSON aliases are not deduplicated in any logical statistic. *)
let fold_json ?(canonical=(fun _ -> ())) ~scalar ~container root =
 let work=ref[`Visit(root,0)] and values=ref[] and active=ref[] and visited=ref 0 in
 while !work<>[] do match !work with
 | []->()
 | `Visit(value,depth)::rest ->
   require(depth<=4096)"v4-value-depth";incr visited;
   require(!visited<=node_cap)"v4-value-constructor-work";
   work:=rest;
   (match value with
    | (`List xs|`Tuple xs) as value ->
      let raw=Obj.repr value in require(not(List.exists(fun x->x==raw)!active))"v4-json-cycle";
      active:=raw:: !active;
      let kind=match value with `List _->"list"|_->"tuple"in
      canonical("["^quote kind^",[");
      work:=`Sequence(kind,"",List.map(fun x->"",x)xs,[],depth,raw):: !work
    | `Assoc xs ->
      let raw=Obj.repr value in require(not(List.exists(fun x->x==raw)!active))"v4-json-cycle";
      active:=raw:: !active;canonical "[\"assoc\",[";work:=`Sequence("assoc","",xs,[],depth,raw):: !work
    | `Variant(name,Some child) ->
      require(String.length name<=262144)"v4-variant-name";
      let raw=Obj.repr value in require(not(List.exists(fun x->x==raw)!active))"v4-json-cycle";
      active:=raw:: !active;canonical("[\"variant-some\","^quote(C.hex name)^",");work:=`Sequence("variant-some",name,["",child],[],depth,raw):: !work
    | _->let encoded=Yojson.Safe.to_string(C.tag value)in
      canonical encoded;values:=scalar value encoded:: !values)
 | `Sequence(kind,name,[],done_,_,raw)::rest ->
   work:=rest;canonical(if kind="variant-some" then "]" else "]]");
   (match !active with x::xs when x==raw->active:=xs|_->raise(C.Incomplete "v4-active-path"));
   values:=container kind name(List.rev done_):: !values
 | `Sequence(kind,name,(key,value)::xs,done_,depth,raw)::rest ->
   require(String.length key<=262144)"v4-assoc-key";
   if done_<>[] then canonical ",";
   if kind="assoc" then canonical("["^quote(C.hex key)^",");
   work:=`Visit(value,depth+1)::`Collect(kind,name,key,xs,done_,depth,raw)::rest
 | `Collect(kind,name,key,xs,done_,depth,raw)::rest ->
   (match !values with value::tail->values:=tail;
     if kind="assoc" then canonical "]";
     work:=`Sequence(kind,name,xs,(key,value)::done_,depth,raw)::rest
    |_->raise(C.Incomplete "v4-fold-stack"))
 done;
 match !values with [value]->value|_->raise(C.Incomplete "v4-fold-result")
let measure ?canonical value = fold_json ?canonical ~scalar:(fun value text->scalar_stats ~encoded:text value) ~container:container_stats value
let scratch_put t text =
 (* Fixed16MiB allocation precedes source conversion; each write is checked
    before copying. This is current-field canonical scratch within128MiB, not
    an expanded tagged tree, a new snapshot budget, or a growing Buffer. *)
 require(String.length text<=byte_cap-t.scratch_used)"v4-current-field-canonical-bytes";
 Bytes.blit_string text 0 t.scratch t.scratch_used(String.length text);
 t.scratch_used<-t.scratch_used+String.length text
let slice t offset length put =
 require(offset>=0&&length>=0&&offset<=t.used-length)"v4-store-span";
 let at=ref 0 in while !at<length do
  let n=min 4096(length- !at)in put(Bytes.sub_string t.store(offset+ !at)n);at:= !at+n done
let remember_import t ~sequence ~origin ~role ~offset ~bytes value =
 require(role="pre"||role="posts")"v4-import-role";
 let st=measure value in require(st.b=bytes)"v4-import-canonical-span";
 let k=origin^":"^role in require(not(Hashtbl.mem t.imports k))"v4-import-duplicate";
 require(Hashtbl.length t.imports<8192)"v4-import-registry";
 Hashtbl.add t.imports k {sequence;role;offset;bytes;stats=st}
let run_entries t n =
 require(di t n 0=2)"v4-private-run-kind";
 let relative=di t n 28 in
 match Yojson.Safe.from_string(Bytes.sub_string t.store(di t n 4+relative)(di t n 8-relative))with
 | `List xs->require(List.length xs=di t n 24&&List.length xs<=64)"v4-private-run-arity";xs
 | _->raise(C.Incomplete "v4-private-run")
let entries t n =
 let count=di t n 24 in let current=ref(di t n 28)and runs=ref[]and got=ref count in
 while !current>=0 do
  let r= !current in require(r<n&&di t r 0=2)"v4-private-run-backedge";
  let width=di t r 24 in require(di t r 20+width= !got)"v4-private-run-offset";
  runs:=r:: !runs;got:= !got-width;current:=di t r 16
 done;
 require(!got=0)"v4-private-run-total";
 List.concat_map(run_entries t)!runs
let hex_of_bytes_scalar t n =
 require(di t n 0=1)"v4-private-key-type";
 match Yojson.Safe.from_string(key t n)with
 | `List[`String "bytes";`String hex]->hex
 |_->raise(C.Incomplete "v4-private-key-bytes")
let stream_value t root put =
 let todo=ref[`Value(root,0)]and visits=ref 0 in
 while !todo<>[] do match !todo with
 | []->()
 | `Text s::rest->todo:=rest;put s
 | `Value(n,depth)::rest ->
  require(n>=0&&n<t.next&&depth<=4096)"v4-private-view";
  incr visits;require(!visits<=node_cap)"v4-resolved-view-work";todo:=rest;
  (match di t n 0 with
  | 1->slice t(di t n 4)(di t n 8)put
  | 3->slice t(di t n 16)(di t n 20)put
  | (4|5|6|7) as code ->
    let xs=entries t n in
    if code=7 then (
     put "[\"variant-some\",\"";
     slice t(di t n 4+di t n 32)(di t n 36)put;put "\",";
     (match xs with [child]->todo:=`Value(from_id child,depth+1)::`Text "]":: !todo
      |_->raise(C.Incomplete "v4-private-variant")))
    else(let kind=if code=4 then"list"else if code=5 then"tuple"else"assoc"in
      put("["^quote kind^",[");todo:=`Entries(xs,code=6,depth+1):: !todo)
  |_->raise(C.Incomplete "v4-run-is-not-value"))
 | `Entries([],_,_)::rest->todo:=rest;put "]]"
 | `Entries(x::xs,assoc,depth)::rest ->
   let tail=(if xs=[]then[]else[`Text ","])@(`Entries(xs,assoc,depth)::rest)in
   if assoc then(match x with `List[key;value]->
     put("["^quote(hex_of_bytes_scalar t(from_id key))^",");
     todo:=`Value(from_id value,depth)::`Text "]"::tail
     |_->raise(C.Incomplete "v4-private-assoc-entry"))
   else todo:=`Value(from_id x,depth)::tail
 done
let make_run t put ~assoc previous start xs =
 let mode=if assoc then"assoc"else"seq"in
 let prev=if previous<0 then `Null else idj previous in
 let prefix=quote mode^","^Yojson.Safe.to_string prev^","^string_of_int start^","in
 let text=prefix^Yojson.Safe.to_string(`List xs)in
 define t ~put ~op:"run"~key_text:text ~code:2 ~st:zero
  ~attrs:[12,(if assoc then 1 else 0);16,previous;20,start;24,List.length xs;28,String.length prefix]
let encode t put value =
 let scalar ?encoded value =
  let text=match encoded with Some text->text|None->Yojson.Safe.to_string(C.tag value)in
  let st=scalar_stats ~encoded:text value in
  require(st.rw<=1048576&&st.tw<=1048576)"v4-definition-words";
  define t ~put ~op:"scalar"~key_text:text~code:1~st~attrs:[]in
 let container kind name children =
  let st=container_stats kind name(List.map(fun(k,n)->k,stats t n)children)in
  require(st.n<=node_cap&&st.d<=4096)"v4-definition-expanded-work";
  let assoc=kind="assoc"in
  let edges=List.map(fun(k,n)->if assoc then `List[idj(scalar(`String k));idj n]else idj n)children in
  let rest=ref edges and previous=ref(-1)and start=ref 0 in
  while !rest<>[] do
   let chunk=ref[]in for _=1 to 64 do match !rest with
    |[]->()|x::xs->chunk:=x:: !chunk;rest:=xs done;
   let xs=List.rev !chunk in previous:=make_run t put ~assoc !previous !start xs;
   start:= !start+List.length xs
  done;
  let variant=kind="variant-some"in let name_text=if variant then quote(C.hex name)else"null"in
  let text=quote kind^","^name_text^","^string_of_int !start^","^
    (if !previous<0 then"null"else quote(id !previous))in
  let code=if kind="list"then 4 else if kind="tuple"then 5 else if assoc then 6 else 7 in
  define t ~put ~op:"value"~key_text:text~code~st
   ~attrs:[24,!start;28,!previous;32,String.length(quote kind)+2;36,2*String.length name]in
 fold_json ~canonical:(scratch_put t) ~scalar:(fun value text->scalar ~encoded:text value) ~container value
let import t put ~sequence ~origin ~role ~admit value =
 let target=match Hashtbl.find_opt t.imports(origin^":"^role)with
 | Some x->x|None->raise(C.Incomplete "v4-missing-expanded-import")in
 require(target.sequence<=t.committed_sequence&&target.sequence<sequence)"v4-import-not-closed";
 let actual=measure ~canonical:(scratch_put t) value in
 admit actual;
 require(actual=target.stats&&t.scratch_used=target.bytes)"v4-import-value-drift";
 (* The two allowed PRE/POST candidates compare complete canonical bytes;
    pointer identity and hashes never establish actual-value equality. *)
 let same=ref true and digest=Hash.create()and at=ref 0 in
 while !at<target.bytes do
  let width=min 4096(target.bytes- !at)in
  let piece=Bytes.sub_string t.store(target.offset+ !at)width in
  for i=0 to width-1 do
   if Bytes.get t.scratch(!at+i)<>piece.[i]then same:=false done;
  Hash.update digest piece;at:= !at+width
 done;
 require !same "v4-import-value-drift";
 let text=string_of_int target.sequence^","^quote role^","^string_of_int target.bytes^","^quote(Hash.finish digest)in
 define t ~put ~op:"import"~key_text:text~code:3~st:actual
  ~attrs:[16,target.offset;20,target.bytes]
let association entries=container_stats "assoc" "" entries
let completed t=List.rev t.observations
(* Test-only observation of the exact source field AFTER the fused equality
   witness. Disabled in every ordinary capture; no reconstructed native state
   or control-supplied value feeds production serialization. *)
let field_observer = ref None
let emit t ~sequence ~source ~phase ~kind ~name ~parent ~alternative ~expanded ~native:(public,ordinal)
 ~fields ~integer_bits ~put =
 require(not t.opened&&Option.is_none t.pending)"v4-nested-snapshot";
 require(String.length name<=4096&&public>=0&&ordinal>=0)"v4-snapshot-metadata";
 t.opened<-true;
 let roles=if phase="normalized-state"then["pre";"state";"substitution";"posts"]
  else if phase="test-created"then["state";"posts";"verification_posts";"entry_rank"]
  else raise(C.Incomplete "v4-snapshot-phase")in
 require(List.map fst fields=roles)"v4-snapshot-fields";
 let line xs=let text=Yojson.Safe.to_string(`List xs)^"\n"in
  require(String.length text<=1048576)"v4-line-cap";put text in
 line[`String"snapshot-begin";`Int sequence;`String phase;`String kind;`String(C.hex name);
  `Int parent;`Int alternative;`Int expanded;`List[`Int public;`Int ordinal];
  `String"this-session-current-preprocessed-program";`List(List.map(fun r->`String r)roles)];
 let origin=origin_key ~source ~parent ~alternative ~expanded in
 let atom x=scalar_stats x in
 let native_stats=container_stats "list" ""["",atom(`Int public);"",atom(`Int ordinal)]in
 let full_stats payload=association["kind",atom(`String kind);"name",atom(`String name);
  "raw_parent",atom(`Int parent);"alternative",atom(`Int alternative);"expanded",atom(`Int expanded);
  "native_id",native_stats;"pred_defs_ref",atom(`String"this-session-current-preprocessed-program");"payload",payload]in
 let admitted=ref[]in
 let admit role st =
  let partial=(role,st):: !admitted in
  let payload=association(List.rev partial)in let full=full_stats payload in
  (* Saturated cached contributions are checked BEFORE any resolved/import
     target is followed. Shared strings/occurrences are never reset by fields. *)
  require(full.n<=node_cap&&full.d<=4096)"v4-expanded-tagged-work";
  require(full.rs<=string_cap&&full.ts<=string_cap)"v4-expanded-snapshot-strings";
  require(payload.j<=8*node_cap&&payload.jd<=16384&&payload.b<=byte_cap)"v4-expanded-canonical-work";
  admitted:=partial in
 let h=Hash.create()and emitted=ref 0 and field_hashes=ref[]in
 let output text=emitted:= !emitted+String.length text;
  require(!emitted<=byte_cap)"v4-canonical-byte-accounting";Hash.update h text in
 output "[\"assoc\",[";
 let roots=List.mapi(fun i(role,build)->
  t.scratch_used<-0;
  let value=build()in
  let n=if phase="normalized-state"&&(role="pre"||role="posts")
   then import t put ~sequence ~origin ~role ~admit:(admit role) value
   else let n=encode t put value in admit role(stats t n);n in
  let st=stats t n in require(st.b=t.scratch_used)"v4-source-canonical-size";
  if i>0 then output ",";output("["^quote(C.hex role)^",");
  let fh=Hash.create()and at=ref 0 in
  (* This is the mandatory canonical payload/hash stream, fused with the
     complete source-owned witness for ALL four fields. Source canonical bytes
     were emitted during dictionary construction, not a second source walk.
     No whole tagged field is built, and scratch is overwritten per field. *)
  stream_value t n(fun text->
   require(String.length text<=t.scratch_used- !at)"v4-actual-resolved-length";
   for k=0 to String.length text-1 do
    require(text.[k]=Bytes.get t.scratch(!at+k))"v4-actual-resolved-value" done;
   at:= !at+String.length text;Hash.update fh text;output text);
  require(!at=t.scratch_used)"v4-actual-resolved-length";
  Option.iter(fun observe->observe ~phase ~kind ~name ~parent ~alternative ~expanded
    ~native:(public,ordinal) ~role value) !field_observer;
  field_hashes:=(role,`String(Hash.finish fh)):: !field_hashes;output "]";
  line[`String"field";`String role;idj n];role,n)fields in
 output "]]";
 let payload=association(List.map(fun(role,n)->role,stats t n)roots)in
 let full=full_stats payload in
 (* Slots1-6 use FULL old data; slots7-8/hash/bytes use payload only. Root's
    sealed usage interpretation34ae551d... retains the actual old authorities. *)
 require(full.rw-payload.rw<=8192&&full.tw-payload.tw<=8192)"v4-fixed-metadata-words";
 require(full.n<=node_cap&&full.d<=4096)"v4-expanded-tagged-work";
 require(full.rs<=string_cap&&full.ts<=string_cap)"v4-expanded-snapshot-strings";
 require(payload.j<=8*node_cap&&payload.jd<=16384&&payload.b<=byte_cap)"v4-expanded-canonical-work";
 let used=integer_bits()in require(used<=1048576)"v4-shared-Z";
 require(!emitted=payload.b)"v4-canonical-byte-total";
 let digest=Hash.finish h in
 let usage=[full.rw;full.tw;full.rs;full.ts;full.n;full.d;payload.j;payload.jd;used]in
 line[`String"snapshot-end";`Int sequence;
  `List(List.map(fun(role,n)->`List[`String role;idj n])roots);
  `Int payload.b;`String digest;`List(List.map(fun n->`Int n)usage)];
 (* Observation is not a success receipt. Provenance publishes state/test
    counters only after the enclosing physical commit succeeds. *)
 t.pending<-Some(`Assoc["origin",`List[`String kind;`String name;`Int parent;`Int alternative;`Int expanded];
  "native_id",`List[`Int public;`Int ordinal];"phase",`String phase;
  "payload_sha256",`String digest;"payload_bytes",`Int payload.b;
  "usage",`List(List.map(fun n->`Int n)usage);
  "field_sha256",`Assoc(List.rev !field_hashes)])
module For_tests=struct
 let sha256=Hash.text
 let committed_definitions t=t.visible
 let with_field_observer observe f =
  let saved= !field_observer in
  Fun.protect ~finally:(fun()->field_observer:=saved)(fun()->field_observer:=Some observe;f())
 let shape value=let x=measure value in[x.rw;x.tw;x.rs;x.ts;x.n;x.d;x.j;x.jd;x.b]
end
