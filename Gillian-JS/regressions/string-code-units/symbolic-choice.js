"use strict";
var flag = symb();
Assume((flag = true) or (flag = false));
var text = flag ? "é" : "😀";
var first = text.charCodeAt(0);
var ok = flag ? first === 233 : first === 55357;
Assert(ok);
