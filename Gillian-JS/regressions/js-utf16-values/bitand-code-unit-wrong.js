"use strict";
/* @import ../../runtime/JS2JSIL/Internals.jsil */
/** @id check
 @pre (x == #x) * types(#x : Num) * (is-int #x) * (0 <=# #x) * (#x <=# 65535)
 @post ((ret == true) /\ (55296 <=# #x) /\ (#x <=# 56319)) \/ ((ret == false) /\ (! ((55296 <=# #x) /\ (#x <=# 56319))))
*/
function check(x) { return (x & 64512) === 56320; }
