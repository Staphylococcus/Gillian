(* Capture-local transport only. Never changes proof AST/global codecs. *)
exception Incomplete of string
let require ok why = if not ok then raise (Incomplete why)
let fragment_bytes = 1024 * 1024
let hex string =
  let digits = "0123456789abcdef" in
  let n = String.length string in
  require (n <= 262144) "raw string budget";
  String.init (2 * n) (fun i ->
      let c = Char.code string.[i / 2] in
      digits.[if i mod 2 = 0 then c lsr 4 else c land 15])
let unhex string =
  require (String.length string mod 2 = 0 && String.length string <= 524288)
    "hex byte budget";
  let digit = function
    | '0' .. '9' as c -> Char.code c - 48
    | 'a' .. 'f' as c -> Char.code c - 87
    | _ -> raise (Incomplete "noncanonical hex")
  in
  String.init (String.length string / 2) (fun i ->
      Char.chr ((digit string.[2*i] lsl 4) lor digit string.[2*i+1]))

(* Count occurrences, not just shared nodes: derived codecs expand sharing.
   A bounded value walk is a separate precondition, not a claim that encoded
   length bounds converter/runtime auxiliary allocations. *)
let inspect ?(node_limit=32768) ?(word_limit=262144) ?(depth_limit=512)
    ?(string_limit=65536) ?(string_total=262144) value =
  let nodes = ref 0 and words = ref 0 and strings = ref 0 and customs = ref [] in
  let rec walk active depth value =
    incr nodes;
    if not (!nodes <= node_limit && depth <= depth_limit) then
      raise (Incomplete (Printf.sprintf
        "value nodes/depth budget nodes=%d node_limit=%d depth=%d depth_limit=%d nodes_exceeded=%d depth_exceeded=%d"
        !nodes node_limit depth depth_limit
        (if !nodes > node_limit then 1 else 0)
        (if depth > depth_limit then 1 else 0)));
    if not (Obj.is_int value) then (
      require (not (List.exists (fun prior -> prior == value) active))
        "cyclic capture fragment";
      let tag = Obj.tag value and size = Obj.size value in
      words := !words + size + 1;
      require (!words <= word_limit) "value word budget";
      if tag = Obj.string_tag then (
        let n = String.length (Obj.obj value : string) in
        strings := !strings + n;
        require (n <= string_limit && !strings <= string_total) "value string budget")
      else if tag = Obj.double_tag || tag = Obj.double_array_tag then ()
      else if tag = Obj.custom_tag then customs := value :: !customs
      else (
        require (tag < Obj.lazy_tag) "unsupported host shape/closure";
        let active = value :: active in
        for i = 0 to size - 1 do walk active (depth + 1) (Obj.field value i) done))
  in
  walk [] 0 (Obj.repr value); !customs
let guard_plain value =
  require (inspect value = []) "unsupported custom block"
let guard_transport value =
  require (inspect ~node_limit:131072 ~word_limit:1048576 ~depth_limit:2048
    ~string_limit:524288 ~string_total:1048576 value = []) "transport custom block"
let guard_transport_v3 value =
  require (inspect ~node_limit:1048576 ~word_limit:8388608 ~depth_limit:2048
    ~string_limit:524288 ~string_total:1048576 value = []) "transport custom block"
let guard_ast_with_node_limit ?(max_depth=512) node_limit visit value =
  let found = inspect ~node_limit ~depth_limit:max_depth value and allowed = ref [] in
  let visitor = object
    inherit [_] Visitors.iter as super
    method! visit_literal env literal =
      match literal with
      | TypeDef__.Int z ->
          require (Z.numbits z <= 65536) "integer conversion bit budget";
          let raw = Obj.repr z in
          if not (Obj.is_int raw) then allowed := raw :: !allowed
      | _ -> super#visit_literal env literal
  end in
  visit visitor value;
  require
    (List.for_all (fun raw -> List.exists (fun z -> raw == z) !allowed) found)
    "unsupported non-Z custom block"
let guard_ast visit value = guard_ast_with_node_limit 32768 visit value
(* Explicit source-pinned V3 typed-guard contract revision: physical object-edge
   depth2048, node131072. Legacy depth512 and all words/strings/custom/Z,
   transport, frame and shared caps stay fixed; wire schema/policy are unchanged. *)
let guard_ast_v3 visit value =
  guard_ast_with_node_limit ~max_depth:2048 131072 visit value

let rec tag (json : Yojson.Safe.t) : Yojson.Safe.t =
  let list kind values = `List [`String kind; `List (List.map tag values)] in
  match json with
  | `Null -> `List [`String "null"]
  | `Bool b -> `List [`String "bool"; `Bool b]
  | `Int n -> `List [`String "int"; `String (string_of_int n)]
  | `Intlit n -> `List [`String "intlit"; `String (hex n)]
  | `Float f ->
      `List [`String "float64"; `String (Printf.sprintf "%016Lx" (Int64.bits_of_float f))]
  | `String s -> `List [`String "bytes"; `String (hex s)]
  | `List xs -> list "list" xs
  | `Tuple xs -> list "tuple" xs
  | `Assoc xs ->
      `List [`String "assoc";
             `List (List.map (fun (k,v) -> `List [`String (hex k); tag v]) xs)]
  | `Variant (k,None) -> `List [`String "variant-none"; `String (hex k)]
  | `Variant (k,Some v) -> `List [`String "variant-some"; `String (hex k); tag v]
let rec untag (json : Yojson.Safe.t) : Yojson.Safe.t =
  match json with
  | `List [`String "null"] -> `Null
  | `List [`String "bool"; `Bool b] -> `Bool b
  | `List [`String "int"; `String s] ->
      let n = int_of_string s in require (string_of_int n = s) "noncanonical int"; `Int n
  | `List [`String "intlit"; `String s] -> `Intlit (unhex s)
  | `List [`String "float64"; `String s] ->
      require (String.length s = 16 && String.for_all
        (function '0'..'9' | 'a'..'f' -> true | _ -> false) s) "float bits";
      `Float (Int64.float_of_bits (Int64.of_string ("0x" ^ s)))
  | `List [`String "bytes"; `String s] -> `String (unhex s)
  | `List [`String "list"; `List xs] -> `List (List.map untag xs)
  | `List [`String "tuple"; `List xs] -> `Tuple (List.map untag xs)
  | `List [`String "assoc"; `List xs] ->
      `Assoc (List.map (function
        | `List [`String k; v] -> (unhex k, untag v)
        | _ -> raise (Incomplete "association entry")) xs)
  | `List [`String "variant-none"; `String k] -> `Variant (unhex k,None)
  | `List [`String "variant-some"; `String k; v] -> `Variant (unhex k,Some (untag v))
  | _ -> raise (Incomplete "unknown/malformed lossless node")
let rec equal a b =
  let pairs xs ys = List.length xs = List.length ys && List.for_all2 equal xs ys in
  match a,b with
  | `Null,`Null -> true | `Bool x,`Bool y -> x=y | `Int x,`Int y -> x=y
  | `Intlit x,`Intlit y | `String x,`String y -> String.equal x y
  | `Float x,`Float y -> Int64.equal (Int64.bits_of_float x) (Int64.bits_of_float y)
  | `List x,`List y | `Tuple x,`Tuple y -> pairs x y
  | `Assoc x,`Assoc y -> List.length x=List.length y &&
      List.for_all2 (fun (k,v) (l,w) -> k=l && equal v w) x y
  | `Variant (k,None),`Variant (l,None) -> k=l
  | `Variant (k,Some v),`Variant (l,Some w) -> k=l && equal v w
  | _ -> false
let checked ?(version=1) ?(guard=guard_plain) ~to_json ~of_json value =
  require (version=1 || version=2 || version=3) "capture codec version";
  let guard_stage stage guard value =
    try guard value with
    | Incomplete why -> raise (Incomplete (why ^ " stage=" ^ stage))
  in
  guard_stage "typed-input" guard value;
  let original = to_json value in
  let transport_guard = if version=3 then guard_transport_v3 else guard_transport in
  guard_stage "derived-json" (if version=1 then guard_plain else transport_guard) original;
  let encoded = tag original in
  if version=2 || version=3 then guard_stage "tagged-payload" transport_guard encoded;
  let wire = Yojson.Safe.to_string encoded in
  require (String.length wire <= fragment_bytes) "encoded fragment1MiB cap";
  let restored = untag (Yojson.Safe.from_string wire) in
  require (equal original restored) "transport tree/float-bit/raw-byte mismatch";
  match of_json restored with
  | Error why -> raise (Incomplete ("typed fragment decoder: " ^ why))
  | Ok decoded ->
      guard_stage "typed-decoded" guard decoded;
      require (equal original (to_json decoded)) "typed roundtrip mismatch";
      encoded

(* V4 parent accounting deliberately has no container-depth acceptance rule.
   All occurrence/word/string/custom bounds remain the V3 original-parent
   bounds. Worklist and active-path tracking count repeated shared occurrences;
   no recursive list/record traversal and no pointer deduplication. *)
let inspect_parent_v4 value =
  let nodes=ref 0 and words=ref 0 and strings=ref 0 and customs=ref [] in
  let active=ref [] and work=ref [`Enter (Obj.repr value)] in
  while !work<>[] do
    match !work with
    | [] -> ()
    | `Leave raw :: rest ->
        work:=rest;
        (match !active with x::xs when x==raw -> active:=xs
         | _ -> raise (Incomplete "V4 active path accounting"))
    | `Enter raw :: rest ->
        work:=rest;incr nodes;
        require (!nodes<=131072) "V4 parent node budget";
        if not (Obj.is_int raw) then (
          require (not (List.exists (fun x -> x==raw) !active))
            "cyclic capture parent";
          let tag=Obj.tag raw and size=Obj.size raw in
          words:= !words+size+1;require (!words<=262144) "V4 parent word budget";
          if tag=Obj.string_tag then (
            let n=String.length (Obj.obj raw : string) in
            strings:= !strings+n;
            require (n<=65536 && !strings<=262144) "V4 parent string budget")
          else if tag=Obj.double_tag || tag=Obj.double_array_tag then ()
          else if tag=Obj.custom_tag then customs:=raw:: !customs
          else (
            require (tag<Obj.lazy_tag) "unsupported host shape/closure";
            active:=raw:: !active;work:=`Leave raw:: !work;
            for i=size-1 downto 0 do work:=`Enter (Obj.field raw i):: !work done))
  done;
  !customs
let check_parent_customs_v4 found allowed =
  require (List.for_all (fun raw -> List.exists (fun z -> raw==z) allowed) found)
    "unsupported non-Z custom block in V4 parent"

(* Explicit V4 leaf entrypoint reuses unchanged V3 transport and leaf guard
   machinery. Legacy checked ~version:4 remains rejected. *)
let checked_v4 ?guard ~to_json ~of_json value =
  checked ~version:3 ?guard ~to_json ~of_json value
