"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == 42)
*/
function check() {
  var flag = false;
  /* @invariant (this == undefined) * scope(flag: true) */
  while (flag) { flag = false; }
  return flag;
}
