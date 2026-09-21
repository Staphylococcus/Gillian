function check(ok) { Assert(ok); }
function invalid(text) {
 var caught = false;
 try { JSON.parse(text); } catch (error) { caught = error instanceof SyntaxError; }
 check(caught);
}
invalid("[1,]"); invalid("{\"a\":}"); invalid("01"); invalid("1."); invalid("\"\\u00xx\"");
var cycle = {}; cycle.self = cycle;
var caught = false;
try { JSON.stringify(cycle); } catch (error) { caught = error instanceof TypeError; }
check(caught);
var token = {}, object = {};
Object.defineProperty(object, "x", { enumerable: true, get: function () { throw token; } });
caught = false;
try { JSON.stringify(object); } catch (error) { caught = error === token; }
check(caught);
