module

import Consumer.API

-- This second module receives Sail transitively, without importing private declarations.
example (value : BitVec n) :
    Consumer.decodeBits value = Vector.ofFn (fun i => value.getLsb i) := rfl

example [Sail.ArchSem.Arch] :
    MonadExcept (Sail.Error Unit) (Sail.ArchSem.PreSailME Unit Nat) := inferInstance
