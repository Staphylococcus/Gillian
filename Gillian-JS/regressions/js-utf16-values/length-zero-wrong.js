"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (s == #s) * types(#s : Str)
@post (ret == 0)
*/
function check(s) { return s.length; }
