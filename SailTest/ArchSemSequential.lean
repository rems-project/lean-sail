import Sail.ArchSemSequential

open Sail Sail.ArchSem Sail.ArchSem.PreSail

-- The sequential interpreter chooses zero from a nonempty finite choice,
-- and fails without changing state when there is no possible choice.
example [Arch] (s : SequentialState Arch.register_type) :
    (interpretSailEffects (choose_fin 1 : PreSailM Unit (Fin 1))).run s =
      .ok (0 : Fin 1) s := by rfl

example [Arch] (s : SequentialState Arch.register_type) :
    (interpretSailEffects (choose_fin 0 : PreSailM Unit (Fin 0))).run s =
      .error .Unreachable s := by rfl
