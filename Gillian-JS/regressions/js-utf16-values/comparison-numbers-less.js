"use strict";
/**
@id check
@pre (a v== #a) * (b v== #b) * types(#a : Num, #b : Num)
@post ((ret == true) /\ (#a <# #b)) \/ ((ret == false) /\ (! (#a <# #b)))
*/
function check(a, b) { return a < b; }
