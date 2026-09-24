"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil */
/** @id check
 @pre (s == #s) * types(#s : Str) * LanguageString(#s)
 @post (ret == true)
*/
function check(s) {
  var len = s.length;
  var count = 0;
  var pos = 0;
  var value;
  /* @invariant scope(s: #s) * scope(len: #len) * scope(count: #count) * scope(pos: #pos) * scope(value: #value) * types(#s : Str, #len : Num, #count : Num, #pos : Num) * (#len == s-len(#s)) * (#len <=# 9007199254740991) * (is-int #len) * (is-int #count) * (is-int #pos) * (0 <=# #count) * (#count <=# #pos) * (#pos <=# #len) * LanguageString(#s) [bind: #pos, #count, #value] variant(9007199254740991 - #pos) */
  while (false) { value = 1; }
  if (pos < len) { return true; }
  return false;
}
