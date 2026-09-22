"use strict";
/** @id count
 @pre (this == undefined) * (len v== #len) * types(#len : Num) * (is-int #len) * (0 <=# #len) * (#len <=# 4294967295)
 @post (ret <=# #len) * (#len <=# ret)
*/
function count(len) {
  var i = 0;
  /* @invariant (this == undefined) * scope(len: #len) * scope(i: #index) * types(#index : Num, #len : Num) * (is-int #index) * (is-int #len) * (0 <=# #index) * (#index <=# #len) * (#len <=# 4294967295) [bind: #index] variant(4294967295 - #index) */
  while (i < len) { i = i + 1; }
  return i;
}
