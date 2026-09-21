var original = {a: [1]};
var copy = JSON.parse(JSON.stringify(original));
var same = copy.a === original.a;
Assert(same);
