"use strict";
var before = symb_string(), after = symb_string();
Assume(not (before = after));
var original = { value: before };
var alias = original;
alias.value = after;
var valid = original.value === after;
Assert(valid);
