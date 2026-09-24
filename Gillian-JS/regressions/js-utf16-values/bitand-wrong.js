"use strict";
/* @import ../../runtime/JS2JSIL/Internals.jsil */
/** @id check
 @pre (x v== #x) * (y v== #y) * types(#x : Num, #y : Num)
 @post (ret == 42)
*/
function check(x, y) { return x & y; }
