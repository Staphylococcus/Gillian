"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil */
/** @id check
 @pre (this == undefined) * (str == #s) * types(#s : Str) * LanguageString(#s)
 @post (ret v== -0)
*/
function check(str) { return str.length; }
