function check(ok) { Assert(ok); }
var original = { z: [1, { a: true }], a: null };
var encoded = JSON.stringify(original);
check(encoded === "{\"z\":[1,{\"a\":true}],\"a\":null}");
var copy = JSON.parse(encoded);
check(copy !== original && copy.z !== original.z && copy.z[1] !== original.z[1]);
original.z[1].a = false;
check(copy.z[1].a === true && copy.a === null);
