"use strict";
/* @import ../../runtime/JS2JSIL/Internals.jsil */
/** @id check
 @pre (x v== #x) * types(#x : Num)
 @post (ret == false)
*/
function check(x) { return (x & 64512) === 56320; }
