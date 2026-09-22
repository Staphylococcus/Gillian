module Legacy_symbolic = JSILSMemory.M

module Symbolic = struct
  include Gillian.Symbolic.Legacy_s_memory.Modernize (Legacy_symbolic)

  (* These concrete primitives access/update finite native heap maps; enumeration
     visits a finite property list. None executes JavaScript or invokes a getter,
     setter, proxy or callback. Higher-level JS helpers still need their own
     proofs. Logical producer/consumer actions are deliberately not admitted. *)
  let is_action_total name arity =
    let open Javert_utils.JSILNames in
    match arity with
    | 1 -> name = delObj || name = getAllProps || name = getMetadata
    | 2 -> name = alloc || name = getCell || name = delCell
    | 3 -> name = setCell
    | _ -> false

  let execute_action name heap pc args =
    let run checked_args = execute_action name heap pc checked_args in
    let args =
      if !Config.Verification.total then
        Legacy_symbolic.prepare_total_action name heap pc.pfs pc.gamma args
      else args
    in
    run args
end

module Concrete = JSILCMemory.M
module External = External.M
module SHeap = SHeap
module SFVL = SFVL
module Utf16 = Javert_utils.Utf16
