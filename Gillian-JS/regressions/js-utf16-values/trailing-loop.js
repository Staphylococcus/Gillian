"use strict";
/** @id check
 @pre (this == undefined)
 @post (ret == 1) */
function check() {
  var i = 0;
  /* @invariant scope(i: #i) * types(#i : Num) * (is-int #i) * (0 <=# #i) * (#i <=# 1) [bind: #i] variant(1 - #i) */
  while (i < 1) {
    i++;
    /* @tactic assert(scope(i: #seen)) [bind: #seen]; assert((#seen == 1)) */
  }
  return i;
}
