"use strict";
/**
@id check
@pre (a == #a) * types(#a : Str)
@post (ret == "string")
*/
function check(a) { return typeof a; }
