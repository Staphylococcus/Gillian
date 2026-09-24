"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil
 @import CharCodeAtContext.jsil */
/** @id check
 @pre (this == undefined) * (s == #s) * (pos v== #pos) * (count v== #count) * types(#s : Str, #pos : Num, #count : Num) * (is-int #pos) * (is-int #count) * (0 <=# #count) * (#count <=# #pos) * (#pos <=# s-len(#s)) * LanguageString(#s) * CharCodeAtContext()
 @post CharCodeAtContext() * types(ret : Bool)
*/
function check(s, pos, count) {
  var len = s.length;
  var rank = 9007199254740991 - pos;
  var value;
  if (pos < len) {
    count++;
    value = s.charCodeAt(pos++);
    if (value >= 55296 && value <= 56319 && pos < len) {
      value = s.charCodeAt(pos);
      return (value & 64512) === 56320;
    }
  }
  return false;
}
