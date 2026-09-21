function check(ok) { Assert(ok); }
var order = "";
var first = { valueOf: function () { order += "a"; return 65; } };
var second = { valueOf: function () { order += "b"; return 66; } };
check(String.fromCharCode(first, second) === "AB");
check(order === "ab");
var token = {};
var caught = false;
try { String.fromCharCode({ valueOf: function () { throw token; } }, first); }
catch (error) { caught = error === token; }
check(caught && order === "ab");
caught = false;
try { String.prototype.trim.call(null); }
catch (error) { caught = error instanceof TypeError; }
check(caught);
caught = false;
try { String.prototype.trim.call({ toString: function () { throw token; } }); }
catch (error) { caught = error === token; }
check(caught);
