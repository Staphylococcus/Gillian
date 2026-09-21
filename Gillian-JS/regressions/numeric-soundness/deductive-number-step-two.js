"use strict";
/**
@id incrementTwo
@pre (n == #n) * types(#n : Num) * (9007199254740992 <=# #n) * (#n <=# 9007199254740994)
@post (#n <# ret)
*/
function incrementTwo(n) { return n + 2; }
