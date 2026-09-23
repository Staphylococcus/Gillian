"use strict";
/**
@id check
@pre (a == #a) * (b == #b) * types(#a : Str, #b : Str)
@post (ret == (#b ++ #a))
*/
function check(a, b) { return a + b; }
