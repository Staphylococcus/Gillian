"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/**
@id check
@pre (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharAtContext()
@post CharAtContext() * (((! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))) /\ (ret == s-nth(#s, num_to_int(#index)))) \/ (((num_to_int(#index) <# 0) \/ (s-len(#s) <=# num_to_int(#index))) /\ (ret == "")))
*/
function check(s, index) { var first = s.charAt(index); return s.charAt(index); }
