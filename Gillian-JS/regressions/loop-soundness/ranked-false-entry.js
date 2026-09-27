"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == 42)
*/
function check() {
  /* @invariant (False) variant(0) */
  for (; false;) { }
  return 42;
}
