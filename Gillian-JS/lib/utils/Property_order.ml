(* OrdinaryOwnPropertyKeys: array indices first, then creation order. The
   input list already has creation order; stable sorting preserves other keys. *)
let index key =
  match Int64.of_string_opt key with
  | Some n when n >= 0L && n < 4294967295L && Int64.to_string n = key -> Some n
  | _ -> None

let sort keys =
  List.stable_sort
    (fun a b ->
      match (index a, index b) with
      | Some a, Some b -> Int64.compare a b
      | Some _, None -> -1
      | None, Some _ -> 1
      | None, None -> 0)
    keys
