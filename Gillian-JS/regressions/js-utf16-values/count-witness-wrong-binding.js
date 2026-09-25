"use strict";
/** @pred nounfold pure CountStep(next : Num) :
 [step: #previous] types(#previous : Num) * (next == #previous + 1); */
/** @id check
 @pre (this == undefined) * (n == #n) * types(#n : Num) * (#n == 0)
 @post (ret == #n + 1) */
function check(n) {
  var result = n + 1;
  /* @tactic assert(scope(result: #next) * types(#next : Num)) [bind: #next]; fold CountStep(#next) [step with (#previous := #n + 1)] */
  return result;
}
