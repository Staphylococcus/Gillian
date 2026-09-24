"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil */
/**
@id check
@pre (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * JSObjGeneral($lstr_proto, $lobj_proto, "String", true) * DataPropGen($lstr_proto, "charAt"; $lsp_charAt, true, false, true) * JSBIFunction($lsp_charAt; "SP_charAt", 1)
@post ((! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))) /\ (ret == s-nth(#s, num_to_int(#index)))) \/ (((num_to_int(#index) <# 0) \/ (s-len(#s) <=# num_to_int(#index))) /\ (ret == ""))
*/
function check(s, index) { return s.charAt(index); }
