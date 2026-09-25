"use strict";
/** @id check
 @pre (this == undefined) * (pos v== #pos) * (len v== #len) * types(#pos : Num, #len : Num) * (is-int #pos) * (is-int #len) * (0 <=# #pos) * (#pos <=# #len) * (! (#pos <# #len)) * (! (#pos v== -0)) * (! (#len v== -0))
 @post (ret v== #len)
*/
function check(pos, len) { return pos; }
