function check(ok) { Assert(ok); }
check(JSON.stringify({a: 1, z: 2}, ["z", "a", "z"]) === "{\"z\":2,\"a\":1}");
var order = "";
var parsed = JSON.parse("[1,2]", function(key, value) { order += key; return key === "0" ? undefined : value; });
check(order === "01" && !("0" in parsed) && parsed[1] === 2);
var object = { toJSON: function(key) { return key === "x" ? 9 : 8; } };
check(JSON.stringify({x: object}) === "{\"x\":9}");
check(JSON.stringify([undefined, NaN, Infinity]) === "[null,null,null]");
check(JSON.stringify(undefined) === undefined);
