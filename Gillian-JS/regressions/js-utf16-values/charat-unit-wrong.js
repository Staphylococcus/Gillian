"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/**
@id check
@pre (#s == "😀") * (#index == 1) * (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharAtContext()
@post CharAtContext() * ((ret == s-nth(#s, 0)))
*/
function check(s, index) { return s.charAt(index); }
