module

public import Sail

@[expose] public section

namespace Consumer

-- Export a runtime-dependent API through the umbrella import.
def decodeBits (value : BitVec n) : Vector Bool n := Sail.bitvec_to_vecbool value

theorem decodeBits_eq (value : BitVec n) :
    decodeBits value = Vector.ofFn (fun i => value.getLsb i) := rfl

end Consumer
