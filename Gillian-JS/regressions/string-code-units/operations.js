function check(ok) { Assert(ok); }
var text = "Aé😀Z";
check(text.length === 5);
check(text[1] === "é");
check(text[2] === "\ud83d");
check(text[3] === "\ude00");
check(text.charAt(2) === "\ud83d");
check(text.slice(2, 4) === "😀");
check(text.slice(-3, -1) === "😀");
check(text.substring(4, 2) === "😀");
check(text.indexOf("😀") === 2);
check(text.lastIndexOf("Z") === 4);
check("😀" === "\ud83d\ude00");
check("\ud83d" + "\ude00" === "😀");
check("😀" < "\ue000");
var object = { "😀": 7 };
check(object["\ud83d\ude00"] === 7);
check(String.fromCharCode() === "");
check(String.fromCharCode(65, 233, 55357, 56832) === "Aé😀");
check(String.fromCharCode(-1, 65536, 65.9) === "\uffff\u0000A");
check(String.fromCharCode(NaN, Infinity, -Infinity) === "\u0000\u0000\u0000");
check(" \ufeff\u2000é😀\u2029\u3000".trim() === "é😀");
check("\u180e\u0085".trim() === "\u180e\u0085");
check(eval("\u0022😀\u0022") === "😀");
check(Function("return \u0022😀\u0022")() === "😀");
function 𐐀(𐐁) { return 𐐁 + 1; }
check(𐐀(6) === 7);
