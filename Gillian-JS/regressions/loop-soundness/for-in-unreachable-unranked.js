/* @import Object.jsil */
"use strict";
/** @id check
    @pre (this == undefined) * (enter == false)
    @post (ret == 42)
*/
function check(enter) {
  if (enter) {
    for (var key in undefined) { }
  }
  return 42;
}
