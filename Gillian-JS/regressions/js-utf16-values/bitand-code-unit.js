"use strict";
/* @import ../../runtime/JS2JSIL/Internals.jsil */
/** @id check
 @pre (x == #x) * types(#x : Num) * (is-int #x) * (0 <=# #x) * (#x <=# 65535)
 @post ((ret == true) /\ (56320 <=# #x) /\ (#x <=# 57343)) \/ ((ret == false) /\ (! ((56320 <=# #x) /\ (#x <=# 57343))))
*/
function check(x) { return (x & 64512) === 56320; }
