"use strict";
/** @id check
    @pre (this == undefined) * (exitEarly == #exitEarly) * types(#exitEarly : Bool)
    @post (ret == true)
*/
function check(exitEarly) {
  var flag = true;
  /* @invariant (this == undefined) * scope(flag: true) * scope(exitEarly: #exitEarly) * types(#exitEarly : Bool) */
  while (flag) {
    if (exitEarly) { break; }
    flag = false;
  }
  return flag;
}
