/* @import ../../runtime/JS2JSIL/Init.jsil
 @import ../../runtime/JS2JSIL/String.jsil
 @import CharCodeAtContext.jsil */
/** @toprequires emp
 @topensures CharCodeAtContext() * scope(check: #caller) * JSFunctionObject(#caller; "check", {{$lg}}, 2, #prototype) * scope(emptyResult: #emptyResult) * (#emptyResult v== nan) * scope(negative: #negative) * (#negative v== nan) * scope(outside: #outside) * (#outside v== nan) * scope(infinite: #infinite) * (#infinite v== nan) * scope(nanResult: 65)
*/
"use strict";
/** @id check */
function check(s, index) { return s.charCodeAt(index); }
var emptyResult = check("", 0);
var negative = check("A", -1);
var outside = check("A", 1);
var infinite = check("A", 1 / 0);
var nanResult = check("A", 0 / 0);
