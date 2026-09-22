"use strict";
var slots = [1, null, 2];
var n = slots.filter(function (item) { return item !== null && item !== undefined; }).length;
Assert(n = 2);
