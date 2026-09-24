"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil
 @import CharCodeAtContext.jsil */
/** @id check
 @pre (this == undefined) * (s == #s) * types(#s : Str) * LanguageString(#s) * CharCodeAtContext()
 @post CharCodeAtContext() * types(ret : Bool)
*/
function check(s) {
  var len = s.length;
  var count = 0;
  var pos = 0;
  var value;
  if (pos < len) {
    count++;
    value = s.charCodeAt(pos++);
    if (value >= 55296 && value <= 56319 && pos < len) { return true; }
  }
  return false;
}
