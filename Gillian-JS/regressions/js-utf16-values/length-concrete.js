"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre emp
@post (ret == true)
*/
function check() {
  return "".length === 0 && "\0".length === 1 && "A\u00e9\uffff".length === 3 &&
    "\ud83d\ude00".length === 2 && "\ud800".length === 1 && "\udfff".length === 1 &&
    "\0A\u00e9\ud83d\ude00\ud800\uffff".length === 7;
}
