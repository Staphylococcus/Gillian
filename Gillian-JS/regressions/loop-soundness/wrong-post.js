"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == 42)
*/
function check() {
  var flag = true;
  /* @invariant (this == undefined) * scope(flag: #flag) * types(#flag : Bool) [bind: #flag] */
  while (flag) { flag = false; }
  return flag;
}
