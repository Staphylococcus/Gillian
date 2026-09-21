var value = symb_string();
try { JSON.stringify(value); } catch (error) { }
Assert(true);
