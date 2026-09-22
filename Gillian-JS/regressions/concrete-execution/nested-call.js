"use strict";
function outer(value) {
 var object = { value: value };
 function inner() { return object.value + 1; }
 return inner();
}
if (outer(41) !== 42) throw new Error("Wrong nested call result");
"nested call ready";
