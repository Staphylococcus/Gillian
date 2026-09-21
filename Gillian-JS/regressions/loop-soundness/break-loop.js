"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == 42)
*/
function check() {
  var flag = true;
  var answer = 42;
  /* @invariant (this == undefined) * scope(flag: #flag) * types(#flag : Bool) [bind: #flag] */
  while (flag) { break; }
  return answer;
}
