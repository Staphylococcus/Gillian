function check(ok) { Assert(ok); }
var value = JSON.parse("{\"__proto__\":1,\"constructor\":2,\"z\":3,\"z\":4}");
check(Object.prototype.hasOwnProperty.call(value, "__proto__"));
check(Object.getPrototypeOf(value) === Object.prototype);
check(value.__proto__ === 1 && value.constructor === 2 && value.z === 4);
check(JSON.stringify(value) === "{\"__proto__\":1,\"constructor\":2,\"z\":4}");
