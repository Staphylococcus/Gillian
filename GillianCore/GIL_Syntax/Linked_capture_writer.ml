module C = Linked_capture_codec
external probe_fd : Unix.file_descr -> int64 array = "gillian_capture_probe_fd"
external probe_path : string -> int64 array = "gillian_capture_probe_path"
external probe_at : Unix.file_descr -> string -> int64 array = "gillian_capture_probe_at"
external open_root : string -> Unix.file_descr = "gillian_capture_open_root"
external create_at : Unix.file_descr -> string -> Unix.file_descr = "gillian_capture_create_at"
type io = {
  probe_fd : Unix.file_descr -> int64 array;
  probe_path : string -> int64 array;
  probe_at : Unix.file_descr -> string -> int64 array;
  open_root : string -> Unix.file_descr;
  create_at : Unix.file_descr -> string -> Unix.file_descr;
  write : Unix.file_descr -> bytes -> int -> int -> int;
  fsync : Unix.file_descr -> unit;
  close : Unix.file_descr -> unit;
}
let system_io = {probe_fd;probe_path;probe_at;open_root;create_at;
                 write=Unix.write;fsync=Unix.fsync;close=Unix.close}
type member = {name:string; mutable state:int64 array}
type t = {
  root:string; dir:Unix.file_descr; root_id:int64 array; io:io;
  limit:int64; mutable intended:int64; mutable written:int64;
  mutable members:member list; mutable active:(Unix.file_descr*member) option;
  mutable failed:string option; mutable sealed:bool; mutable dir_closed:bool;
  mutable phases:int; mutable close_uncertain:bool;
}
let cap = 67108864L
let shape s = C.require (Array.length s=9) "physical probe shape"
let same_id a b = a.(0)=b.(0) && a.(1)=b.(1) && a.(5)=b.(5) && a.(6)=b.(6) && a.(7)=b.(7) && a.(8)=b.(8)
let same a b = same_id a b && a.(2)=b.(2) && a.(3)=b.(3) && a.(4)=b.(4)
let first_failure t e = if t.failed=None then t.failed<-Some (Printexc.to_string e)
let healthy t = C.require (t.failed=None && not t.sealed && not t.dir_closed) "capture writer permanently failed/sealed"
let operation t f = try healthy t;f () with e -> first_failure t e;raise e
let verify_root t =
  let named=t.io.probe_path t.root and opened=t.io.probe_fd t.dir in
  shape named;shape opened;
  C.require (same_id named t.root_id && same_id named opened && named.(7)=1L && named.(8)=448L &&
    Unix.realpath t.root=t.root) "capture root identity/alias";
  named
let usage t =
  let root=verify_root t in
  let names=Sys.readdir t.root |> Array.to_list |> List.sort String.compare in
  let expected=List.map (fun m->m.name) t.members |> List.sort String.compare in
  C.require (names=expected) "unexpected capture namespace entry";
  let total=List.fold_left (fun n m ->
      let s=t.io.probe_at t.dir m.name in shape s;
      C.require (same s m.state && s.(7)=0L && s.(5)=1L && s.(0)=root.(0))
        "closed/current capture identity/allocation changed";
      Int64.add n s.(3)) root.(3) t.members in
  C.require (same root (verify_root t)) "capture root changed during measurement";
  C.require (total>=0L && total<=t.limit) "capture physical64MiB cap";total
let create ?(io=system_io) ?(limit=cap) root =
  C.require (limit>0L && limit<=cap) "capture limit may only tighten64MiB";
  C.require (not(Filename.is_relative root) && not(String.contains root '\000')) "absolute capture root";
  let parent=Filename.dirname root in
  C.require (Unix.realpath parent=parent && root=Filename.concat parent (Filename.basename root) &&
    Filename.basename root<>"." && Filename.basename root<>"..") "capture parent alias";
  let ps=Unix.lstat parent in
  C.require (ps.Unix.st_kind=Unix.S_DIR && ps.Unix.st_uid=Unix.getuid ()) "capture parent owner";
  (try ignore(Unix.lstat root);raise(C.Incomplete "fresh capture root required")
   with Unix.Unix_error(Unix.ENOENT,_,_)->());
  Unix.mkdir root 0o700;
  let dir=io.open_root root in
  try
    let root_id=io.probe_fd dir and named=io.probe_path root in shape root_id;shape named;
    C.require (same_id root_id named && root_id.(7)=1L && root_id.(8)=448L && root_id.(6)=Int64.of_int(Unix.getuid ())) "capture root owner/descriptor";
    let t={root;dir;root_id;io;limit;intended=0L;written=0L;members=[];active=None;
           failed=None;sealed=false;dir_closed=false;phases=0;close_uncertain=false} in
    ignore(usage t);t
  with e -> (try io.close dir with _ -> ());raise e
let refresh ?size t fd m =
  let opened=t.io.probe_fd fd and named=t.io.probe_at t.dir m.name in
  shape opened;shape named;
  let expected=match size with Some n->n |None->m.state.(2) in
  C.require (same_id opened m.state && same opened named && opened.(2)=expected && named.(7)=0L && named.(5)=1L)
    "capture descriptor/named identity";
  m.state<-named
let precharge t bytes =
  let current=usage t in
  let unit=(verify_root t).(4) in
  C.require (unit>0L && unit<=1048576L) "capture allocation unit";
  let n=Int64.of_int bytes in
  let rounded=Int64.mul (Int64.div (Int64.add n (Int64.pred unit)) unit) unit in
  let charge=Int64.add (Int64.mul 2L rounded) (Int64.mul 16L unit) in
  C.require (Int64.add current charge<=t.limit) "capture prospective physical cap"
let start t index = operation t (fun () ->
    C.require (t.active=None && index=t.phases && index>=0 && index<=2) "capture phase/file order";
    precharge t 0;
    let name=Printf.sprintf "%08d.jsonl" index in
    let fd=t.io.create_at t.dir name in
    try
      let state=t.io.probe_fd fd and named=t.io.probe_at t.dir name in shape state;shape named;
      C.require (same state named && state.(7)=0L && state.(5)=1L && state.(2)=0L &&
        state.(8)=384L && state.(6)=t.root_id.(6) && state.(0)=t.root_id.(0)) "exclusive capture file identity";
      let m={name;state} in t.members<-t.members@[m];t.active<-Some(fd,m);ignore(usage t)
    with e -> t.active<-None;(try t.io.close fd with close_e -> t.close_uncertain<-true;first_failure t close_e);raise e)
let write t text = operation t (fun () ->
    let n=String.length text in
    C.require (n<=C.fragment_bytes) "capture frame1MiB cap";
    let bytes=Bytes.of_string text in
    let fd,m=match t.active with Some pair->pair |None->raise(C.Incomplete "no capture phase file") in
    refresh t fd m;precharge t n;
    let intended=Int64.add t.intended (Int64.of_int n) in
    C.require (intended<=t.limit) "capture cumulative encoded64MiB cap";
    t.intended<-intended; (* Before any write; partial attempts cannot reset it. *)
    let at=ref 0 in
    while !at<n do
      let wrote=t.io.write fd bytes !at (n- !at) in
      C.require (wrote>0 && wrote<=n- !at) "zero/invalid capture write progress";
      at:= !at+wrote;t.written<-Int64.add t.written (Int64.of_int wrote)
    done;
    t.io.fsync fd;refresh ~size:(Int64.add m.state.(2) (Int64.of_int n)) t fd m;ignore(usage t))
let close_phase t = operation t (fun () ->
    let fd,m=match t.active with Some pair->pair |None->raise(C.Incomplete "capture phase not open") in
    t.io.fsync fd;refresh t fd m;
    t.active<-None;
    (try t.io.close fd with e->t.close_uncertain<-true;raise e);
    t.io.fsync t.dir;
    let current=t.io.probe_at t.dir m.name in
    C.require (same current m.state) "capture allocation/identity changed after close";
    ignore(usage t);t.phases<-t.phases+1)
let abort t why =
  if not t.sealed then (
    if t.failed=None then t.failed<-Some why;
    (match t.active with None->() |Some(fd,_)->
      t.active<-None;(try t.io.close fd with e->t.close_uncertain<-true;first_failure t e));
    if not t.dir_closed then (t.dir_closed<-true;try t.io.close t.dir with e->t.close_uncertain<-true;first_failure t e);
    t.sealed<-true)
let finish t manifest =
  try
    C.require (t.phases=2 && t.active=None) "both capture phases must close first";
    start t 2;write t manifest;close_phase t;
    operation t (fun ()->ignore(usage t);t.dir_closed<-true;
      (try t.io.close t.dir with e->t.close_uncertain<-true;raise e);t.sealed<-true)
  with e -> first_failure t e;abort t "capture finish failed";raise e
let snapshot t =
  (t.failed,t.sealed,t.dir_closed && not t.close_uncertain,t.active=None && not t.close_uncertain,t.intended,t.written,t.phases,t.close_uncertain)
