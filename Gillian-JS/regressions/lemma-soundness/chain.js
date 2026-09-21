"use strict";
/* @pred Chain(x) :
     (x == null),
     JSObject(x) * DataProp(x, "next"; #next) * Chain(#next);
*/
/** @id scan
    @pre (this == undefined) * GlobalObject() * scope(scan: #f) * JSFunctionObject(#f; "scan", _, _, _) * (lst == #lst) * Chain(#lst)
    @post GlobalObject() * scope(scan: #f) * JSFunctionObject(#f; "scan", _, _, _) * Chain(#lst) * (ret == 42)
*/
function scan(lst) {
  if (lst === null) return 42;
  return scan(lst.next);
}
