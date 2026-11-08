module

public import Sail

@[expose] public section

namespace Consumer

-- Export a runtime-dependent API through the umbrella import.
def decodeBits (value : BitVec n) : Vector Bool n := Sail.bitvec_to_vecbool value

end Consumer
