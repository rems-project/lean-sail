import Sail

section UndefinedRangeTests

inductive TestReg | r deriving DecidableEq, Hashable

local instance : Sail.ArchSem.Arch where
  addr_size := 64
  addr_space := Unit
  CHERI := false
  cap_size_log := 0
  register := TestReg
  register_type := fun _ => Unit
  mem_acc := Unit
  mem_acc_is_explicit := fun _ => true
  mem_acc_is_ifetch := fun _ => false
  mem_acc_is_ttw := fun _ => false
  mem_acc_is_relaxed := fun _ => true
  mem_acc_is_rel_acq_rcpc := fun _ => false
  mem_acc_is_rel_acq_rcsc := fun _ => false
  mem_acc_is_standalone := fun _ => false
  mem_acc_is_exclusive := fun _ => false
  mem_acc_is_atomic_rmw := fun _ => false
  trans_start := Unit
  trans_end := Unit
  abort := Unit
  barrier := Unit
  cache_op := Unit
  tlbi := Unit
  exn := Unit
  sys_reg_id := Unit

open Sail.ArchSem

/-- The values `undefined_range` can produce, one per resolution of its choice. -/
def rangeValues (m : PreSailM Unit Int) : List Int :=
  match m with
  | .impure (.inr n) k =>
      (List.finRange (n : Nat)).filterMap fun i =>
        match k i with
        | .pure v => some v
        | _ => none
  | .pure v => [v]
  | _ => []

-- Sail's `range(low, high)` is inclusive.
#guard rangeValues (PreSail.undefined_range 0 3) == [0, 1, 2, 3]
#guard rangeValues (PreSail.undefined_range 5 5) == [5]
#guard rangeValues (PreSail.undefined_range 5 4) == []
#guard (match (interpretSailEffects (PreSail.undefined_range (ue := Unit) 5 5)).run default with
  | .ok v _ => v == 5
  | .error _ _ => false)

end UndefinedRangeTests
