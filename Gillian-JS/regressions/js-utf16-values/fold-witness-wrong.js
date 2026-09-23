"use strict";
/** @pred Target(s) : (s == #w) * (#w == "x"); */
/**
@id check
@pre emp
@post (ret == true)
*/
function check() {
  /* @tactic fold Target("x") [pick with (#w := "y")] */
  return true;
}
