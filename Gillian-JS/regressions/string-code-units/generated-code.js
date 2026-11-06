"use strict";
var quote = Function("return \"\\\"\";")();
var slash = Function("return \"\\\\\";")();
var evaluated = eval("\"\\\"\"");
var ok = quote.charCodeAt(0) === 34 && slash.charCodeAt(0) === 92
  && evaluated.charCodeAt(0) === 34;
Assert(ok);

// Eval creates a real call frame inside an ordinary function call. Both normal
// and caught-error returns must release only that frame's temporary roots.
function nestedEvalPins() {
  var saved = { value: 7 };
  return eval("saved.value + 1") === 8 && saved.value === 7;
}
function caughtEvalPins() {
  var saved = { value: 9 };
  try { eval("throw 11"); }
  catch (error) { return error === 11 && saved.value === 9; }
  return false;
}
var evalPinsOk = nestedEvalPins() && caughtEvalPins();
Assert(evalPinsOk);
