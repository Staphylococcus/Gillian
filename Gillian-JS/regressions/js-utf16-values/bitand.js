"use strict";
/* @import ../../runtime/JS2JSIL/Internals.jsil */
/** @id check
 @pre (x v== #x) * (y v== #y) * types(#x : Num, #y : Num)
 @post types(ret : Num) * (is-int ret) * (-2147483648 <=# ret) * (ret <=# 2147483647)
*/
function check(x, y) { return x & y; }
