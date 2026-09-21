"use strict";

var n = symb_number(); Assume((n >= 9007199254740992) and (n <= 9007199254740994));
var valid = n + 1 > n;
Assert(valid);