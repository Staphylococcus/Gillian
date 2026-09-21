"use strict";
/** @id forever
    @pre (this == undefined)
    @post (ret == 42)
*/
function forever() {
  /* @invariant (this == undefined) */
  while (true) {}
  return 42;
}
