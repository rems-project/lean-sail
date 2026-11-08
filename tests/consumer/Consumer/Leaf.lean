module

import Sail.Common

-- An ordinary leaf import must expose executable definitions to kernel reduction.
example : Sail.vecbool_to_bitvec #v[true, false, true] = (5 : BitVec 3) := by decide

example (value : BitVec n) :
    Sail.bitvec_to_vecbool value = Vector.ofFn (fun i => value.getLsb i) := rfl
