"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import LanguageString.gil */
/**
@id check
@pre (s == #s) * types(#s : Str) * LanguageString(#s)
@post (is-int ret)
*/
function check(s) { return s.length; }
