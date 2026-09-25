"use strict";
/** @pred nounfold pure CountStep(next : Num) :
 [step: #previous] types(#previous : Num) * (next == #previous + 1); */
/** @id check
 @pre (this == undefined)
 @post (ret == 1) */
function check() {
  var n = -0;
  var result = n + 1;
  /* @tactic assert(scope(n: #previous) * scope(result: #next) * types(#previous : Num, #next : Num)) [bind: #previous, #next]; fold CountStep(#next) [step with (#previous := #previous)] */
  return result;
}
