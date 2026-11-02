(* GIL n-ary Operators *)

type t = TypeDef__.nop =
  (* List concatenation *)
  | LstCat
  | LstInsert
  | Utf16Sub  (** Proof-only UTF-16 slice with mathematical Int start/count *)
  (* Set management *)
  | SetUnion
  | SetInter
[@@deriving eq, ord]

let to_yojson = TypeDef__.nop_to_yojson
let of_yojson = TypeDef__.nop_of_yojson

let str (x : t) =
  match x with
  | LstCat -> "l+"
  | LstInsert -> "l-insert"
  | Utf16Sub -> "u16-sub"
  | SetUnion -> "-u-"
  | SetInter -> "-i-"
