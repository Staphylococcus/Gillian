"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import CharAtContext.jsil */
/**
@id check
@pre (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharAtContext()
@post types(ret : Str) * CharAtContext() * (((! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))) /\ (ret == s-nth(#s, num_to_int(#index)))) \/ (((num_to_int(#index) <# 0) \/ (s-len(#s) <=# num_to_int(#index))) /\ (ret == "")))
*/
function check(s, index) { return s.charAt(index); }

/** @id twice
@pre (firstS == #firstS) * (firstIndex v== #firstIndex) * types(#firstS : Str, #firstIndex : Num) * (fn == #fn) * (s == #s) * (index v== #index) * types(#s : Str, #index : Num) * CharAtContext() * JSFunctionObject(#fn; "check", #scope, 2, #prototype)
@post types(ret : Str) * CharAtContext() * (((! (num_to_int(#index) <# 0)) /\ (! (s-len(#s) <=# num_to_int(#index))) /\ (ret == s-nth(#s, num_to_int(#index)))) \/ (((num_to_int(#index) <# 0) \/ (s-len(#s) <=# num_to_int(#index))) /\ (ret == ""))) * JSFunctionObject(#fn; "check", #scope, 2, #prototype)
*/
function twice(fn, firstS, firstIndex, s, index) { var first = fn(firstS, firstIndex); var second = fn(s, index); return 42; }
