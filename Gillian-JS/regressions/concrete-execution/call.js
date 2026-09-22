"use strict";
function addOne(value) { return value + 1; }
if (addOne(41) !== 42) throw new Error("Wrong concrete call result");
"concrete call ready";
