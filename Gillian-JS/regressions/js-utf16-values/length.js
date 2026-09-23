"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (s == #s) * types(#s : Str)
@post (ret == s-len(#s))
*/
function check(s) { return s.length; }
