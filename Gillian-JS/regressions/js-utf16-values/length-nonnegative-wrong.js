"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (s == #s) * types(#s : Str)
@post (! (0 <=# ret))
*/
function check(s) { return s.length; }
