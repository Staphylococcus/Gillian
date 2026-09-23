"use strict";
/**
@id check
@pre (b == #b) * (s == #s) * types(#b : Bool, #s : Str)
@post (ret == true)
*/
function check(b, s) {
  if (b) {
    if (s < "x") return false;
    return false;
  }
  return true;
}
