"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil */
/** @id check
 @pre (s == #s) * types(#s : Str) * LanguageString(#s)
 @post (! (ret <=# 9007199254740991))
*/
function check(s) { return s.length; }
