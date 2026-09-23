"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (s == #s) * (raw v== #index) * (index v== num_to_int(#index)) * types(#s : Str, #index : Num)
@post ((ret == -1) /\ (num_to_int(#index) <# 0)) \/ ((ret == 0) /\ (! (num_to_int(#index) <# 0)) /\ (s-len(#s) <=# num_to_int(#index))) \/ ((ret == 1) /\ (! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))))
*/
function check(s, index, raw) {
  if (index < 0) return 2;
  if (s.length <= index) return 0;
  return 1;
}
