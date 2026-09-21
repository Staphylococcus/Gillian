"use strict";

/**
@id increment
@pre (n == #n) * types(#n : Num) * (9007199254740992 <=# #n) * (#n <=# 9007199254740994)
@post (#n <# ret)
*/
function increment(n) { return n + 1; }
