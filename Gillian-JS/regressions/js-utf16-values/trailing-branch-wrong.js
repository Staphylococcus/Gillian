"use strict";
/** @id check
 @pre (this == undefined) * (b == #b) * types(#b : Bool)
 @post (ret == 1) \/ (ret == 2) */
function check(b) {
  var x;
  if (b) {
    x = 1;
    /* @tactic assert(scope(x: #seen)) [bind: #seen]; assert((#seen == 2)) */
  } else {
    x = 2;
    /* @tactic assert(scope(x: #seen)) [bind: #seen]; assert((#seen == 2)) */
  }
  return x;
}
