"use strict";
/** @id check
    @pre (this == undefined)
    @posterr (ret == 42)
*/
function check() {
  var flag = true;
  var answer = 42;
  /* @invariant (this == undefined) * scope(flag: #flag) * types(#flag : Bool) [bind: #flag] */
  while (flag) { throw 42; }
  throw 42;
}
