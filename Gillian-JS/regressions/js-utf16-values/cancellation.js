"use strict";
/**
@id check
@pre (a == #a) * (b == #b) * (c == #c) * types(#a : Str, #b : Str, #c : Str)
@post ((ret == true) /\ (#b == #c)) \/ ((ret == false) /\ (! (#b == #c)))
*/
function check(a, b, c) { return a + b === a + c; }
