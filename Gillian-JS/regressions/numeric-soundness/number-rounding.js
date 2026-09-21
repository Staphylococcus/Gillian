"use strict";

var n = symb_number(); Assume(n = 9007199254740992);
var value = n + 1;
var valid = value === n;
Assert(valid);