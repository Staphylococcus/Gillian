"use strict";
/**
@id check
@pre (o == #o) * (key == #key) * (value v== #value) * types(#key : Str) * JSObject(#o) * DataProp(#o, #key; #old)
@post (ret v== #value) * JSObject(#o) * DataProp(#o, #key; #value)
*/
function check(o, key, value) { o[key] = value; return o[key]; }
