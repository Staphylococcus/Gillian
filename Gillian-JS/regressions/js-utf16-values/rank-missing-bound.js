"use strict";
/** @id check
 @pre (this == undefined) * (pos v== #pos) * (len v== #len) * types(#pos : Num, #len : Num) * (is-int #pos) * (is-int #len) * (0 <=# #pos) * (#pos <# #len) * (#pos v== 9007199254740992) * (#len v== 9007199254740994)
 @post types(ret : Num) * (is-int ret) * (0 <=# ret) * (ret <# (9007199254740991 - #pos))
*/
function check(pos, len) {
  pos++;
  return 9007199254740991 - pos;
}
