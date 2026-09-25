"use strict";
/* @import Ucs2Arithmetic.gil */
/** @id check
 @pre (this == undefined) * (count v== #count) * (pos v== #pos) * (len v== #len) * types(#count : Num, #pos : Num, #len : Num) * (is-int #count) * (is-int #pos) * (is-int #len) * (0 <=# #count) * (#count <=# #pos) * (#pos <# #len) * (#len <=# 9007199254740991)
 @post types(ret : Num) * (is-int ret) * (ret == #count + 1) * (0 <=# ret) * (ret <=# (#pos + 1))
*/
function check(count, pos, len) {
  count++;
  count++;
  pos++;
  /* @tactic assert(scope(pos: #after) * types(#after : Num)) [bind: #after]; apply Ucs2NumericAdvance(#count, #pos, #after, #len) */
  return count;
}
