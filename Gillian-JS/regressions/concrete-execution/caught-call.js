"use strict";
function fail() { throw 5; }
var value;
try { fail(); } catch (error) { value = error; }
if (value !== 5) throw new Error("Wrong caught call result");
"caught call ready";
