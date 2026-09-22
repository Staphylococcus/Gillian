"use strict";
function addOne(value) { return value + 1; }
var total = 0;
for (var i = 0; i < 8; i++) total += addOne(i);
if (total !== 36) throw new Error("Wrong loop call result");
"loop call ready";
