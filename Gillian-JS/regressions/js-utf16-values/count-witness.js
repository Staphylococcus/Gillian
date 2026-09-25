"use strict";
/** @pred nounfold pure CountStep(next : Num) :
 [step: #previous] types(#previous : Num) * (next == #previous + 1); */
/** @id check
 @pre (this == undefined) * (n == #n) * types(#n : Num) * (is-int #n) * (0 <=# #n) * (#n <=# 9007199254740990)
 @post (ret == #n + 1) */
function check(n) {
  var result = n + 1;
  /* @tactic assert(scope(result: #next) * types(#next : Num)) [bind: #next]; fold CountStep(#next) [step with (#previous := #n)] */
  return result;
}
