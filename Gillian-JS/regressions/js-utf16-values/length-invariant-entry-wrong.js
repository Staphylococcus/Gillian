"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil */
/**
@id check
@pre (s == #s) * types(#s : Str) * LanguageString(#s)
@post (ret == false)
*/
function check(s) {
  var len = s.length;
  var value;
  /* @invariant scope(s: #s) * scope(len: #len) * scope(value: #value) * types(#s : Str, #len : Num) * (#len == s-len(#s)) * LanguageString(#s) [bind: #value] variant(0) */
  while (false) { value = 1; }
  return true;
}
