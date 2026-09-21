"use strict";
var n = symb_number(), low = 1e308, high = 1.1e308;
Assume((n >= low) and (n <= high));
var overflow = n * 2;
var invalid = overflow - overflow;
var valid = overflow === Infinity && invalid !== invalid;
Assert(valid);
