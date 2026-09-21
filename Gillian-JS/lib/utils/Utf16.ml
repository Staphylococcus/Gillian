(* The Flow parser represents JavaScript strings as WTF-8. Decode using the
   same library, preserving lone surrogates and splitting astral code points
   into the two UTF-16 code units observable by JavaScript. *)
let code_units string =
  let encoded = Buffer.create (String.length string) in
  let unsupported () =
    raise (Gillian.Utils.Exceptions.Unsupported "Malformed WTF-8 string")
  in
  let reversed =
    Wtf8.fold_wtf_8
      (fun units _ -> function
        | Wtf8.Malformed -> unsupported ()
        | Wtf8.Point point ->
            if point < 0 || point > 0x10ffff then unsupported ();
            Wtf8.add_wtf_8 encoded point;
            if point < 0x10000 then point :: units
            else
              let offset = point - 0x10000 in
              (0xdc00 + (offset land 0x3ff))
              :: (0xd800 + (offset lsr 10))
              :: units)
      [] string
  in
  (* Wtf8's decoder is permissive about continuation bytes and overlong forms.
     Reject malformed internal strings instead of silently changing their value. *)
  if Buffer.contents encoded <> string then unsupported ();
  List.rev reversed

(* Encode one WTF-8 sequence per code unit (CESU-8). This canonical form makes
   ordinary byte equality, concatenation and ordering agree with UTF-16. *)
let of_code_units units =
  let buffer = Buffer.create (List.length units) in
  List.iter
    (fun unit ->
      if unit < 0 || unit > 0xffff then invalid_arg "UTF-16 code unit";
      Wtf8.add_wtf_8 buffer unit)
    units;
  Buffer.contents buffer

let canonical string = of_code_units (code_units string)

(* The JS source parser expects Unicode scalar UTF-8 for paired surrogates. *)
let source_text string =
  let buffer = Buffer.create (String.length string) in
  let rec append = function
    | high :: low :: rest
      when high >= 0xd800 && high <= 0xdbff && low >= 0xdc00 && low <= 0xdfff ->
        Wtf8.add_wtf_8 buffer (0x10000 + ((high - 0xd800) lsl 10) + low - 0xdc00);
        append rest
    | unit :: _ when unit >= 0xd800 && unit <= 0xdfff ->
        raise
          (Gillian.Utils.Exceptions.Unsupported
             "Lone surrogate in generated JavaScript source")
    | unit :: rest ->
        Wtf8.add_wtf_8 buffer unit;
        append rest
    | [] -> ()
  in
  append (code_units string);
  Buffer.contents buffer

let is_space = function
  | 0x09
  | 0x0a
  | 0x0b
  | 0x0c
  | 0x0d
  | 0x20
  | 0xa0
  | 0x1680
  | 0x2028
  | 0x2029
  | 0x202f
  | 0x205f
  | 0x3000
  | 0xfeff -> true
  | unit -> unit >= 0x2000 && unit <= 0x200a

let trim string =
  let rec drop = function
    | unit :: rest when is_space unit -> drop rest
    | units -> units
  in
  string |> code_units |> drop |> List.rev |> drop |> List.rev |> of_code_units
