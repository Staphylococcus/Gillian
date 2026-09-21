"use strict";
var quote = Function("return \"\\\"\";")();
var slash = Function("return \"\\\\\";")();
var evaluated = eval("\"\\\"\"");
var ok = quote.charCodeAt(0) === 34 && slash.charCodeAt(0) === 92
  && evaluated.charCodeAt(0) === 34;
Assert(ok);
