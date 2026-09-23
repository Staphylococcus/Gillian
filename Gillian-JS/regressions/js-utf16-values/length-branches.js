"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
// raw binds the original Number so the precondition can express ToInteger.
// The unused binding admits every Number, including NaN and infinities.
/**
@id check
@pre (s == #s) * (raw v== #index) * (index v== num_to_int(#index)) * types(#s : Str, #index : Num)
@post ((ret == 0) /\ (s-len(#s) <=# num_to_int(#index))) \/ ((ret == 1) /\ (! (s-len(#s) <=# num_to_int(#index))))
*/
function check(s, index, raw) {
  if (s.length <= index) return 0;
  return 1;
}
