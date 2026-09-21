function check(ok) { Assert(ok); }
var object = { z: 1, a: 2, "10": 3, "2": 4, "01": 5, "4294967295": 6 };
var keys = Object.keys(object);
check(keys[0] === "2" && keys[1] === "10" && keys[2] === "z" && keys[3] === "a" && keys[4] === "01" && keys[5] === "4294967295");
object.z = 7;
keys = Object.keys(object);
check(keys[2] === "z");
delete object.z;
object.z = 8;
keys = Object.keys(object);
check(keys[5] === "z");
