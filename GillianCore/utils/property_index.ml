(** Canonical ECMAScript array-index names (0 through 2^32-2). *)
let of_string key =
  match Int64.of_string_opt key with
  | Some n when n >= 0L && n < 4294967295L && Int64.to_string n = key -> Some n
  | _ -> None

(** Position in an already OrdinaryOwnPropertyKeys-ordered sequence. Ordinary
    names append. Index names precede ordinary names and larger indices. *)
let insertion_position name keys =
  match of_string name with
  | None -> List.fold_left (fun n _ -> Z.succ n) Z.zero keys
  | Some index ->
      let rec find n = function
        | [] -> n
        | key :: rest ->
            (match Option.bind key of_string with
             | None -> n
             | Some other when other > index -> n
             | Some _ -> find (Z.succ n) rest)
      in find Z.zero keys
