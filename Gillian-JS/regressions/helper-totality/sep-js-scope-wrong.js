"use strict";
/** @id answer
 @pre (this == undefined) * (value v== #value) * types(#value : Num)
 @post (ret v== #value)
*/
function answer(value) {
  var local = value;
  /* @tactic assert(scope(local: #captured)) [bind: #captured]; assert((1 == 2)) */
  ;
  return local;
}
