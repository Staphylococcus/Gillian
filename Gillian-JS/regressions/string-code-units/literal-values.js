"use strict";
var key = "\u0022";
var object = {"\u0022": 7};
var ok = key.length === 1 && object[key] === 7 && "\\".length === 1;
Assert(ok);
