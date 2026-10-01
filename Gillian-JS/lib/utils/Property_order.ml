(* OrdinaryOwnPropertyKeys: array indices first, then creation order. The
   input list already has creation order; stable sorting preserves other keys. *)
let index = Gillian.Utils.Property_index.of_string

let sort_by key keys =
  List.stable_sort
    (fun a b ->
      match (index (key a), index (key b)) with
      | Some a, Some b -> Int64.compare a b
      | Some _, None -> -1
      | None, Some _ -> 1
      | None, None -> 0)
    keys

let sort keys = sort_by Fun.id keys
