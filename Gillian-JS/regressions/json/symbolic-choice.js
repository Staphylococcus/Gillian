function check(ok) { Assert(ok); }
var flag = symb();
Assume(typeOf flag = Bool);
var original = flag ? {a: ["é"]} : {a: ["😀"]};
var result = JSON.parse(JSON.stringify(original));
check(result !== original && result.a !== original.a && result.a[0] === original.a[0]);
