/* @import ../../runtime/JS2JSIL/Init.jsil
 @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/** @toprequires emp
 @topensures CharAtContext() * scope(check: #caller) * JSFunctionObject(#caller; "check", {{$lg}}, 2, #prototype)
*/
"use strict";
/** @id check */
function check(s, index) { return s.charAt(index); }
