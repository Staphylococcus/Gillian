"use strict";
/** @id count
 @pre (this == undefined) * (n == #initial) * types(#initial : Num) * (is-int #initial) * (0 <=# #initial) * (#initial <=# 4294967295)
 @post (ret == 0)
*/
function count(n) {
  /* @invariant (this == undefined) * scope(n: #current) * types(#current : Num) * (is-int #current) * (0 <=# #current) * (#current <=# 4294967295) [bind: #current] variant(#current) */
  while (n > 0) { n = n - 1; }
  return n;
}
