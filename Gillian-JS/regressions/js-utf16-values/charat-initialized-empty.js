/* @import ../../runtime/JS2JSIL/Init.jsil
 @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/** @toprequires emp
 @topensures CharAtContext() * scope(check: #caller) * JSFunctionObject(#caller; "check", {{$lg}}, 2, #prototype) * scope(emptyResult: "") * scope(negative: "") * scope(outside: "") * scope(infinite: "") * scope(nanResult: "A")
*/
"use strict";
/** @id check */
function check(s, index) { return s.charAt(index); }
var emptyResult = check("", 0);
var negative = check("A", -1);
var outside = check("A", 1);
var infinite = check("A", 1 / 0);
var nanResult = check("A", 0 / 0);
