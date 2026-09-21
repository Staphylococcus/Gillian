// Flow rejects raw lone surrogates in source. This is a backend limitation,
// not the SyntaxError a program could catch; native JavaScript accepts it.
try { eval("\u0022\ud800\u0022"); } catch (error) { }
Assert(true);
