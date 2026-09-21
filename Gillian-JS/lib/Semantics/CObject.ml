open Gillian.Concrete

type t = { fields : (string, Values.t) Hashtbl.t; mutable order : string list }

let pp fmt (loc, obj, metadata) =
  let pp_kv fmt (prop, value) = Fmt.pf fmt "%s: %a" prop Values.pp value in
  Fmt.pf fmt "@[<h>%s|-> [ %a ], %a@]" loc
    (Fmt.hashtbl ~sep:Fmt.comma pp_kv)
    obj.fields Values.pp metadata

let init () = { fields = Hashtbl.create Config.medium_tbl_size; order = [] }
let get obj prop = Hashtbl.find_opt obj.fields prop

let set obj prop value =
  if not (Hashtbl.mem obj.fields prop) then obj.order <- prop :: obj.order;
  Hashtbl.replace obj.fields prop value

let remove obj prop =
  Hashtbl.remove obj.fields prop;
  obj.order <- List.filter (( <> ) prop) obj.order

let properties obj = Javert_utils.Property_order.sort (List.rev obj.order)
