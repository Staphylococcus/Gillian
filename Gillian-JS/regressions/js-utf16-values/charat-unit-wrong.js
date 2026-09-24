"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (#s == "😀") * (#index == 1) * (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * JSObjGeneral($lstr_proto, $lobj_proto, "String", true) * DataPropGen($lstr_proto, "charAt"; $lsp_charAt, true, false, true) * JSBIFunction($lsp_charAt; "SP_charAt", 1)
@post (ret == s-nth(#s, 0))
*/
function check(s, index) { return s.charAt(index); }
