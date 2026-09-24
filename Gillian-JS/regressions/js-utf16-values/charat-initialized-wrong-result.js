/* @import ../../runtime/JS2JSIL/Init.jsil
 @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/** @toprequires emp
 @topensures CharAtContext() * scope(check: #caller) * JSFunctionObject(#caller; "check", {{$lg}}, 2, #prototype) * scope(ascii: "A") * scope(high: #high) * (#high == s-nth("😀", 0)) * scope(low: #low) * (#low == s-nth("😀", 1)) * scope(lone: #lone) * (#lone == s-nth("𐀀", 0))
*/
"use strict";
/** @id check */
function check(s, index) { return s.charAt(index); }
var ascii = check("AB", 1);
var high = check("😀", 0);
var low = check("😀", 1);
var lone = check("\ud800", 0);
