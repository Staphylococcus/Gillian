"use strict";
var first = "😀".charCodeAt(0);
var wrong = first === 128512;
Assert(wrong);
