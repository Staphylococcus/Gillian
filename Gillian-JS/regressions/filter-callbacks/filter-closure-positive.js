"use strict";
function pick(list, keep) {
  return list.filter(function (x) { return x === keep; }).length;
}
var n = pick([3, 9, 3, 3], 3);
Assert(n = 3);
