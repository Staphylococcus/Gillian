"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharCodeAtContext.jsil */
/** @id check
 @pre (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharCodeAtContext()
 @post CharCodeAtContext() * types(ret : Bool)
*/
function check(s, index) { var value = s.charCodeAt(index); return (value & 64512) === 56320; }
