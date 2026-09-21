"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == false)
*/
function check() {
  var flag = false;
  /* @invariant (this == undefined) * scope(flag: #flag) * types(#flag : Bool) [bind: #flag] */
  while (flag) { flag = false; }
  return flag;
}
