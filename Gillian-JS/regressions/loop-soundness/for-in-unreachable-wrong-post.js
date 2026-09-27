/* @import Object.jsil */
"use strict";
/** @id check
    @pre (this == undefined) * (enter == false)
    @post (ret == 43)
*/
function check(enter) {
  if (enter) {
    /* @invariant (False) variant(0) */
    for (var key in undefined) { }
  }
  return 42;
}
