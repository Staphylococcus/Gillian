"use strict";
/* @import ../../runtime/JS2JSIL/String.jsil
 @import ../../regressions/js-utf16-values/LanguageString.gil
 @import ../../regressions/js-utf16-values/Ucs2Arithmetic.gil
 @import Ucs2Prefix.gil
 @import ../../regressions/js-utf16-values/CharCodeAtContext.jsil */
/** @id ucs2length
 @pre (this == undefined) * (str == #s) * types(#s : Str) * LanguageString(#s) * CharCodeAtContext()
 @post Ucs2Prefix(#s, s-len(#s), s-len(#s), ret) * CharCodeAtContext() * types(ret : Num) * (is-int ret) * (0 <=# ret) * (ret <=# s-len(#s))
*/
function ucs2length(str) {
        var len = str.length;
        var length = 0;
        var pos = 0;
        var value;
        /* @invariant (! (#pos v== -0)) * (! (#len v== -0)) * Ucs2Prefix(#s, #len, #pos, #count) * (this == undefined) * scope(str: #s) * scope(len: #len) * scope(length: #count) * scope(pos: #pos) * scope(value: #value) * types(#s : Str, #len : Num, #count : Num, #pos : Num) * (#len == s-len(#s)) * (#len <=# 9007199254740991) * (is-int #len) * (is-int #count) * (is-int #pos) * (0 <=# #count) * (#count <=# #pos) * (#pos <=# #len) * LanguageString(#s) * CharCodeAtContext() [bind: #pos, #count, #value] variant(9007199254740991 - #pos) */
        while (pos < len) {
          length++;
          value = str.charCodeAt(pos++);
          if (value >= 55296 && value <= 56319 && pos < len) {
            value = str.charCodeAt(pos);
            if ((value & 64512) !== 56320) pos++;
          }
          /* @tactic assert(scope(pos: #next_pos) * scope(length: #count + 1) * types(#next_pos : Num)) [bind: #next_pos]; apply Ucs2NumericAdvance(#count, #pos, #next_pos, #len); fold Ucs2Prefix(#s, #len, #next_pos, #count + 1) [step with (#previous := #pos) and (#previous_count := #count)] */
        }
        /* @tactic assert(#pos v== #len) */
        return length;
      }
