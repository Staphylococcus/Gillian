(* Preparation-only v2. This emits the exact Codec.tag JSON grammar, not an AST
   token protocol. FNV-1a64 is an accidental-corruption transport checksum only;
   the independently observed complete ledger SHA256 remains external authority. *)
module C = Linked_program_capture.Codec
let require = C.require
let chunk_bytes = 16384
let checksum_initial = 0xcbf29ce484222325L
let checksum_update state text =
  let result = ref state in
  String.iter (fun c -> result := Int64.mul
    (Int64.logxor !result (Int64.of_int (Char.code c))) 0x100000001b3L) text;
  !result
let checksum state = Printf.sprintf "%016Lx" state
let checksum_text text = checksum (checksum_update checksum_initial text)
type meter = { mutable words : int; mutable strings : int }
type t = { put : string -> unit; raw : meter; tagged : meter }
type node = t -> unit
let meter () = {words=0; strings=0}
let create put = {put;raw=meter ();tagged=meter ()}
let words meter n =
  require (n >= 0 && meter.words <= 1048576 - n) "v2-transport-word-cap";
  meter.words <- meter.words + n
let string meter n =
  require (n <= 524288 && meter.strings <= 1048576 - n)
    "v2-transport-string-cap";
  (* OCaml64: header plus ceil((bytes + terminator)/8) payload words. *)
  words meter (1 + (n + 8) / 8); meter.strings <- meter.strings + n
let raw_string t s = string t.raw (String.length s)
let tag_string t n = words t.tagged 3; string t.tagged n
let tag_header t name arity =
  (* `List, its list spine, and the `String name constructor/string. *)
  words t.tagged (3 + 3 * arity); tag_string t (String.length name)
let quote t s = t.put (Yojson.Safe.to_string (`String s))
let hex t s =
  let n = String.length s in
  require (n <= 262144) "raw string budget";
  (* Do not allocate the complete hex string; frame sink owns bounded growth. *)
  t.put "\"";
  let digits = "0123456789abcdef" and pair = Bytes.create 2 in
  String.iter (fun c -> let n=Char.code c in
    Bytes.set pair 0 digits.[n lsr 4];Bytes.set pair 1 digits.[n land 15];
    t.put (Bytes.to_string pair)) s;
  t.put "\""
let atom name raw_cost value encoded t =
  words t.raw raw_cost; tag_header t name (if name="null" then 1 else 2);
  t.put "[";quote t name;
  if name<>"null" then (words t.tagged 3;t.put ",";value t;encoded t);
  t.put "]"
let null = atom "null" 0 (fun _ -> ()) (fun _ -> ())
let bool b = atom "bool" 3 (fun t -> t.put (if b then "true" else "false"))
  (fun _ -> ())
let int n t =
  words t.raw 3; let s=string_of_int n in
  tag_header t "int" 2;tag_string t (String.length s);
  t.put "[\"int\",";quote t s;t.put "]"
let bytes s t =
  words t.raw 3;raw_string t s;tag_header t "bytes" 2;
  tag_string t (2 * String.length s);
  t.put "[\"bytes\",";hex t s;t.put "]"
let intlit s t =
  words t.raw 3;raw_string t s;tag_header t "intlit" 2;
  tag_string t (2 * String.length s);
  t.put "[\"intlit\",";hex t s;t.put "]"
let float f t =
  words t.raw 5;tag_header t "float64" 2;tag_string t 16;
  t.put "[\"float64\",";quote t (Printf.sprintf "%016Lx" (Int64.bits_of_float f));t.put "]"
(* iter supplies child nodes one at a time; no event-wide map/tree is built.
   Before each list cell/association pair growth, charge both exact old shapes. *)
let sequence kind iter t =
  words t.raw 3;tag_header t kind 2;words t.tagged 3;
  t.put "[";quote t kind;t.put ",[";
  let first=ref true in
  iter (fun child ->
    words t.raw 3;words t.tagged 3;
    if not !first then t.put ",";first:=false;child t);
  t.put "]]"
let list iter = sequence "list" iter
let tuple iter = sequence "tuple" iter
let assoc iter t =
  words t.raw 3;tag_header t "assoc" 2;words t.tagged 3;
  t.put "[\"assoc\",[";
  let first=ref true in
  iter (fun key child ->
    words t.raw 6;raw_string t key;
    words t.tagged (3 + 3 + 6);tag_string t (2 * String.length key);
    if not !first then t.put ",";first:=false;
    t.put "[";hex t key;t.put ",";child t;t.put "]");
  t.put "]]"
let fields xs = assoc (fun add -> List.iter (fun (k,v) -> add k v) xs)
let values xs = list (fun add -> List.iter add xs)
let variant name child t =
  words t.raw 6;raw_string t name;
  let tag = match child with None -> "variant-none" | Some _ -> "variant-some" in
  let arity=match child with None -> 2 | Some _ -> 3 in
  tag_header t tag arity;tag_string t (2 * String.length name);
  t.put "[";quote t tag;t.put ",";hex t name;
  (match child with None -> () | Some child -> words t.raw 2;t.put ",";child t);
  t.put "]"
(* Iterative replay of one already bounded derived leaf. No tagged copy/string;
   list-spine depth is not semantic depth. Active paths reject forged cycles. *)
let json root t =
  let active=ref [] in
  let work=ref [`Enter root] in
  while !work<>[] do match !work with
  | [] -> ()
  | `Text text::rest -> work:=rest;t.put text
  | `Leave raw::rest -> work:=rest;
      (match !active with x::xs when x==raw -> active:=xs
       | _ -> raise(C.Incomplete "v2-json-active-path"))
  | `Seq []::rest | `Assoc []::rest -> work:=`Text "]]"::rest
  | `Seq (x::xs)::rest ->
      words t.raw 3;words t.tagged 3;
      work:=`Enter x::(if xs=[] then [] else [`Text ","]) @ (`Seq xs::rest)
  | `Assoc ((key,x)::xs)::rest ->
      words t.raw 6;raw_string t key;
      words t.tagged 12;tag_string t (2*String.length key);
      t.put "[";hex t key;t.put ",";
      work:=`Enter x::`Text "]"::
        (if xs=[] then [] else [`Text ","]) @ (`Assoc xs::rest)
  | `Enter value::rest ->
      work:=rest;
      let raw=Obj.repr value in
      require (not(List.exists(fun x -> x==raw) !active)) "cyclic v2 JSON";
      (match value with
       | `Null -> null t | `Bool b -> bool b t | `Int n -> int n t
       | `Intlit s -> intlit s t | `Float f -> float f t | `String s -> bytes s t
       | (`List xs | `Tuple xs) as v ->
           let kind=match v with `List _ -> "list" | _ -> "tuple" in
           words t.raw 3;tag_header t kind 2;words t.tagged 3;
           t.put "[";quote t kind;t.put ",[";
           active:=raw:: !active;work:=`Seq xs::`Leave raw:: !work
       | `Assoc xs ->
           words t.raw 3;tag_header t "assoc" 2;words t.tagged 3;
           t.put "[\"assoc\",[";
           active:=raw:: !active;work:=`Assoc xs::`Leave raw:: !work
       | `Variant (name,None) -> variant name None t
       | `Variant (name,Some child) ->
           words t.raw 8;raw_string t name;
           tag_header t "variant-some" 3;tag_string t (2*String.length name);
           t.put "[\"variant-some\",";hex t name;t.put ",";
           active:=raw:: !active;
           work:=`Enter child::`Text "]"::`Leave raw:: !work)
  done
