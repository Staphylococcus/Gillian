"use strict";
/** @id forever
    @pre GlobalObject() * scope(forever: #f) * JSFunctionObject(#f; "forever", _, _, _)
    @post GlobalObject() * scope(forever: #f) * JSFunctionObject(#f; "forever", _, _, _) * (ret == 42)
*/
function forever() { return forever(); }
