function check(ok) { Assert(ok); }
var value = "é😀\ud800\u0000\n\u0022\\";
var text = JSON.stringify(value);
check(text === "\"é😀\\ud800\\u0000\\n\\\"\\\\\"");
check(JSON.parse(text) === value);
check(JSON.parse("\"\\ud83d\\ude00\"") === "😀");
