"use strict";
var method = String.prototype.charCodeAt;
var a = method.call(123, 1);
var b = method.call(true, 0);
var c = "abc".charCodeAt("1");
var d = "abc".charCodeAt(null);
var e = method.call(new String("é"), false);
var order = "";
var receiver = {toString: function () {order += "s"; return "😀";}};
var index = {valueOf: function () {order += "i"; return 1;}};
var f = method.call(receiver, index);
var ok = a === 50 && b === 116 && c === 98 && d === 97 && e === 233
  && f === 56832 && order === "si";
Assert(ok);
var caughtNull = false, caughtUndefined = false, caughtReceiver = false;
var caughtIndex = false;
try { method.call(null, 0); } catch (err) { caughtNull = err instanceof TypeError; }
try { method.call(undefined, 0); } catch (err) { caughtUndefined = err instanceof TypeError; }
order = "";
try {
  method.call({toString: function () {throw "receiver";}}, index);
} catch (err) { caughtReceiver = err === "receiver" && order === ""; }
try {
  method.call("abc", {valueOf: function () {throw "index";}});
} catch (err) { caughtIndex = err === "index"; }
var throws = caughtNull && caughtUndefined && caughtReceiver && caughtIndex;
Assert(throws);
