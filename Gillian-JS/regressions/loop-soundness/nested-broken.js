"use strict";
/** @id check
    @pre (this == undefined)
    @post (ret == false)
*/
function check() {
  var outer = true;
  var inner = true;
  /* @invariant (this == undefined) * scope(outer: #outer) * types(#outer : Bool) * scope(inner: #inner) * types(#inner : Bool) [bind: #outer, #inner] */
  while (outer) {
    inner = true;
    /* @invariant (this == undefined) * scope(inner: true) */
    while (inner) { inner = false; }
    outer = false;
  }
  return outer;
}
