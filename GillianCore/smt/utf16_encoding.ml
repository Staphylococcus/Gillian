open Simple_smt

let sort = app_ "Seq" [ t_bits 16 ]

let encode string =
  let units = Utils.Utf16.code_units string in
  if Utils.Utf16.of_code_units units <> string then
    raise
      (Utils.Exceptions.Unsupported
         "UTF-16 SMT bridge requires canonical CESU-8");
  match units with
  | [] -> as_type (atom "seq.empty") sort
  | _ -> (
      let units =
        List.map (fun unit -> app_ "seq.unit" [ bv_k 16 (Z.of_int unit) ]) units
      in
      match units with
      | [ unit ] -> unit
      | _ -> app_ "seq.++" units)

let recover expression =
  let rec collect reversed (expression : sexp) =
    match expression with
    | List [ Atom "as"; Atom "seq.empty"; typ ] when typ = sort -> reversed
    | List [ Atom "seq.unit"; unit ] ->
        (* The numeric library also accepts signs/underscores, which are not
           digits in an SMT bitvector literal. Width is checked by to_bits. *)
        let valid_digits prefix digit = function
          | Sexplib.Sexp.Atom text when String.starts_with ~prefix text ->
              String.for_all digit (String.sub text 2 (String.length text - 2))
          | _ -> false
        in
        if
          not
            (valid_digits "#x"
               (function
                 | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
                 | _ -> false)
               unit
            || valid_digits "#b"
                 (function
                   | '0' | '1' -> true
                   | _ -> false)
                 unit)
        then raise (UnexpectedSolverResponse expression);
        let unit = to_bits 16 false unit in
        if Z.sign unit < 0 || Z.gt unit (Z.of_int 0xffff) then
          raise (UnexpectedSolverResponse expression);
        Z.to_int unit :: reversed
    | List (Atom "seq.++" :: (_ :: _ :: _ as parts)) ->
        List.fold_left collect reversed parts
    | _ -> raise (UnexpectedSolverResponse expression)
  in
  try
    let units = collect [] (no_let expression) |> List.rev in
    Some (Utils.Utf16.of_code_units units)
  with UnexpectedSolverResponse _ -> None
