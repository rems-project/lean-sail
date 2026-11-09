import Sail

section LoopTests

instance : MonadLoopLimit (Except String) where
  loopLimit msg := .error msg

def result : Except String Nat → String
  | .ok n => s!"ok {n}"
  | .error e => e

def countWhile (fuel bound : Nat) : Except String Nat :=
  whileFuelM fuel (fun i => pure (i < bound)) 0 (fun i => pure (i + 1))

def countUntil (fuel bound : Nat) : Except String Nat :=
  untilFuelM fuel (fun i => pure (bound ≤ i)) 0 (fun i => pure (i + 1))

-- As Lem's `whileMT` and `untilMT`: `fuel + 1` steps, a step of a `while` loop being a test of
-- its condition (and the body, if it holds), one of an `until` loop the body and the test.
#guard result (countWhile 3 3) == "ok 3"
#guard result (countWhile 4 3) == "ok 3"
#guard result (countUntil 2 3) == "ok 3"
#guard result (countUntil 3 3) == "ok 3"
-- A loop that would need more steps fails instead of returning its current variables.
#guard result (countWhile 2 3) == "whileFuelM: termination limit reached"
#guard result (countUntil 1 3) == "untilFuelM: termination limit reached"

end LoopTests
