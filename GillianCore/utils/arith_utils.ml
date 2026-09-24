(** Utility functions for floating point arithmetic *)

(** Checks if a float is an integer

    Note that [-0] is {b not} considered an integer *)
let is_int (f : float) : bool =
  let f' = float_of_int (int_of_float f) in
  f = f' && copysign 1.0 f = copysign 1.0 f'

(** Checks if a flot is not NaN or infinite *)
let is_normal (f : float) =
  let fc = Float.classify_float f in
  not (fc = FP_infinite || fc = FP_nan)

(** Rounds a float towards 0

    Returns 0 if NaN, and unchanged if infinite*)
let to_int n =
  match classify_float n with
  | FP_nan -> 0.
  | FP_infinite -> n
  | FP_zero -> n
  | FP_normal | FP_subnormal ->
      (if n < 0. then -1. else 1.) *. floor (abs_float n)

(** Same as {!to_int}, but overflows as if it's a signed 32-bit int *)
let to_int32 n =
  match classify_float n with
  | FP_normal | FP_subnormal ->
      let i32 = 2. ** 32. in
      let i31 = 2. ** 31. in
      let posint = (if n < 0. then -1. else 1.) *. floor (abs_float n) in
      let int32bit =
        let smod = mod_float posint i32 in
        if smod = 0. then 0. else if smod < 0. then smod +. i32 else smod
      in
      if int32bit >= i31 then int32bit -. i32 else int32bit
  | _ -> 0.

(** Same as {!to_int32}, but for unsigned 32-bit ints *)
let to_uint32 n =
  match classify_float n with
  | FP_normal | FP_subnormal ->
      let i32 = 2. ** 32. in
      let posint = (if n < 0. then -1. else 1.) *. floor (abs_float n) in
      let int32bit =
        let smod = mod_float posint i32 in
        if smod = 0. then 0. else if smod < 0. then smod +. i32 else smod
      in
      int32bit
  | _ -> 0.

(** Same as {!to_uint32}, but for unsigned 16-bit ints *)
let to_uint16 n =
  match classify_float n with
  | FP_normal | FP_subnormal ->
      let i16 = 2. ** 16. in
      let posint = (if n < 0. then -1. else 1.) *. floor (abs_float n) in
      let int16bit =
        let smod = mod_float posint i16 in
        if smod = 0. then 0. else if smod < 0. then smod +. i16 else smod
      in
      int16bit
  | _ -> 0.

let int64_bitwise_not = Z.lognot
let int64_bitwise_and = Z.logand
let int64_bitwise_or = Z.logor
let int64_bitwise_xor = Z.logxor
let int64_left_shift x y = Z.shift_left x (Z.to_int y)

let int64_right_shift x y =
  let l = Int64.of_float x in
  let r = int_of_float y in
  Int64.to_float (Int64.shift_right l r)

let uint64_right_shift x y =
  let l = Int64.of_float x in
  let r = int_of_float y in
  Int64.to_float (Int64.shift_right_logical l r)

let int32_bitwise_not x = Int32.to_float (Int32.lognot (Int32.of_float x))

let int32_bitwise_and x y =
  (* Give Number AND explicit ToInt32 semantics rather than depending on
     unspecified host conversions outside the signed 32-bit range. The JS
     compiler already converts both operands; applying ToInt32 twice is exact. *)
  Int32.to_float
    (Int32.logand (Int32.of_float (to_int32 x)) (Int32.of_float (to_int32 y)))

let int32_bitwise_or x y =
  Int32.to_float (Int32.logor (Int32.of_float x) (Int32.of_float y))

let int32_bitwise_xor x y =
  Int32.to_float (Int32.logxor (Int32.of_float x) (Int32.of_float y))

let int32_left_shift x y =
  let l = Int32.of_float x in
  let r = int_of_float y mod 32 in
  Int32.to_float (Int32.shift_left l r)

let int32_right_shift x y =
  let l = Int32.of_float x in
  let r = int_of_float y mod 32 in
  Int32.to_float (Int32.shift_right l r)

let uint32_right_shift x y = Z.shift_right x (Z.to_int y)

let uint32_right_shift_f x y =
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let signedx = if x >= i31 then x -. i32 else x in
  let left = Int32.of_float signedx in
  let right = int_of_float y mod 32 in
  let r = Int32.to_float (Int32.shift_right_logical left right) in
  if r < 0. then r +. i32 else r

let uint64_int_right_shift x y = Z.shift_right x (Z.to_int y)

(** ECMAScript's shortest round-tripping binary64 representation. Keep this
    conversion shared by concrete execution and symbolic constant reduction. *)
let float_to_string_inner = Dtoa.ecma_string_of_float

(* Validate ECMAScript's numeric-string grammar before using the native
   decimal/radix parsers. OCaml additionally accepts underscores, signed radix
   prefixes and other spellings that JavaScript must reject. *)
let decimal_string =
  Str.regexp
    {|[+-]?\(Infinity\|\([0-9]+\(\.[0-9]*\)?\|\.[0-9]+\)\([eE][+-]?[0-9]+\)?\)|}

let radix_strings =
  List.map Str.regexp [ "0[xX][0-9a-fA-F]+"; "0[oO][0-7]+"; "0[bB][01]+" ]

let string_to_number string =
  try
    let string = Utf16.trim string in
    let matches pattern =
      Str.string_match pattern string 0
      && Str.match_end () = String.length string
    in
    if string = "" then 0.
    else if matches decimal_string then Float.of_string string
    else if List.exists matches radix_strings then
      Z.to_float (Z.of_string string)
    else nan
  with Failure _ | Invalid_argument _ | Exceptions.Unsupported _ -> nan
