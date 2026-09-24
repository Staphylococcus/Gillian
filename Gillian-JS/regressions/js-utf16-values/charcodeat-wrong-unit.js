"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharCodeAtContext.jsil */
/**
@id check
@pre (#s == "A") * (#index == 0) * (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharCodeAtContext()
@post CharCodeAtContext() * (ret == 66)
*/
function check(s, index) { return s.charCodeAt(index); }
