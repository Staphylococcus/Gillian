function check(ok) { Assert(ok); }
var token = {};
function call() { throw token; }
function loop() {
  var i;
  for (i = 0; i < 1; i++) { }
  call();
}
var caught = false;
try { loop(); } catch (error) { caught = error === token; }
check(caught);
function body() { var i; for (i = 0; i < 1; i++) call(); }
caught = false;
try { body(); } catch (error) { caught = error === token; }
check(caught);
