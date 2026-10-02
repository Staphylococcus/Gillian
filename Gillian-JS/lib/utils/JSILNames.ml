(** Local Actions *)

let aCell = "Cell"
let getCell = "GetCell"
let setCell = "SetCell"
let delCell = "DeleteCell"
let alloc = "Alloc"
let delObj = "DeleteObject"
let getAllProps = "GetAllProps"
let aMetadata = "Metadata"
let getMetadata = "GetMetadata"
let setMetadata = "SetMetadata"
let delMetadata = "DelMetadata"
let aProps = "Props"
let getProps = "getProps"
let setProps = "setProps"
let delProps = "delProps"
let resourceError = "ResourceError"

(* Exclusive complete field-map assertion; these are logical actions only. *)
let aOrderedFields = "OrderedFields"
let getOrderedFields = "GetOrderedFields"
let setOrderedFields = "SetOrderedFields"
let delOrderedFields = "DeleteOrderedFields"

(* The same exclusive footprint, with a checked selected descriptor witness. *)
let aSelectedFields = "SelectedFields"
let getSelectedFields = "GetSelectedFields"
let setSelectedFields = "SetSelectedFields"
let delSelectedFields = "DeleteSelectedFields"
