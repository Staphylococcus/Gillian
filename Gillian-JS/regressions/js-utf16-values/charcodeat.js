"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharCodeAtContext.jsil */
/**
@id check
@pre (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharCodeAtContext()
@post CharCodeAtContext() * (((! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))) /\ (ret == u16-code(#s, num_to_int(#index)))) \/ (((num_to_int(#index) <# 0) \/ (s-len(#s) <=# num_to_int(#index))) /\ (ret v== nan)))
*/
function check(s, index) { return s.charCodeAt(index); }
