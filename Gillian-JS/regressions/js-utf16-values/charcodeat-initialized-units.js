/* @import ../../runtime/JS2JSIL/Init.jsil
 @import ../../runtime/JS2JSIL/String.jsil
 @import CharCodeAtContext.jsil */
/** @toprequires emp
 @topensures CharCodeAtContext() * scope(check: #caller) * JSFunctionObject(#caller; "check", {{$lg}}, 2, #prototype) * scope(ascii: 66) * scope(high: 55357) * scope(low: 56832) * scope(lone: 55296)
*/
"use strict";
/** @id check */
function check(s, index) { return s.charCodeAt(index); }
var ascii = check("AB", 1);
var high = check("😀", 0);
var low = check("😀", 1);
var lone = check("\ud800", 0);
