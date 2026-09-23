"use strict";
/**
@id check
@pre (o == #o) * (n v== #n) * types(#n : Num) * JSObject(#o) * DataProp(#o, num_to_string #n; #value)
@post (ret v== #value) * JSObject(#o) * DataProp(#o, num_to_string #n; #value)
*/
function check(o, n) { return o[n]; }
