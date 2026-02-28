import Sail.Attr
import Sail.ArchSem
import Sail.ConcurrencyInterfaceV1

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

namespace Sail


section PreSailTypes

open ArchSem

/-
class ConcurrencyInterfaceV2.Arch where
  addr_size : Nat
  addr_space : Type
  CHERI : Bool
  cap_size_log : Nat

  mem_acc : Type
  mem_acc_is_explicit : mem_acc -> Bool
  mem_acc_is_ifetch : mem_acc -> Bool
  mem_acc_is_ttw : mem_acc -> Bool
  mem_acc_is_relaxed : mem_acc -> Bool
  mem_acc_is_rel_acq_rcpc : mem_acc -> Bool
  mem_acc_is_rel_acq_rcsc : mem_acc -> Bool
  mem_acc_is_standalone : mem_acc -> Bool
  mem_acc_is_exclusive : mem_acc -> Bool
  mem_acc_is_atomic_rmw : mem_acc -> Bool

  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlbi : Type
  exn : Type
  sys_reg_id : Type
-/

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/

end PreSailTypes

def print_int : String → Int → Unit := fun _ _ => ()

def prerr_int : String → Int → Unit := fun _ _ => ()

def prerr_bits: String → BitVec n → Unit := fun _ _ => ()

def print_endline : String → Unit := fun _  => ()

def prerr_endline : String → Unit := fun _ => ()

def print : String → Unit := fun _ => ()

def prerr : String → Unit := fun _ => ()

end Sail

namespace PreSail

open Sail
open ArchSem

section SailME

open ArchSem
variable [Arch]

/-
variable {Register : Type} {RT : Register → Type} [DecidableEq Register] [Hashable Register]
variable (RT) in
abbrev PreSailME ue α := ExceptT (Error ue ⊕ α) (PreSailM RT c ue)
-/


/-
instance: MonadExceptOf (Error ue) (PreSailME RT c ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)
-/


/- CR clang: so this only throws and catches `Error ue`... -/
/-
instance: MonadExceptOf (Error ue) (PreSailME ue α) where
  throw e := .impure (.Ok (.Err e)) Empty.elim
  tryCatch eff h :=
    let rec tryCatch eff h :=
      match eff with
        | .pure v => .pure v
        | .impure (.Ok (.Err e)) _cont => h e
        | .impure eff cont => .impure eff (fun v => tryCatch (cont v) h)
    tryCatch eff h
-/

/-
def PreSailME.map_error (e : PreSailME ue ε α) (f : ε → ε') : PreSailME ue ε' α :=
  match e with
  | .pure v => .pure v
  | .impure (.Err e) cont => .impure (.Err (f e)) Empty.elim
  | .impure (.Ok eff) cont => .impure (.Ok eff)
    (fun v => PreSailME.map_error (cont (cast (by ) v)) f)

def _root_.ExceptT.map_error [Monad m] (e : ExceptT ε m α) (f : ε → ε') : ExceptT ε' m α :=
  ExceptT.mk <| do
    match ← e.run with
    | .ok x => pure $ .ok x
    | .error e => pure $ .error (f e)

instance [∀ x, CoeT α x α'] :
    CoeT (PreSailME ue α β) e (PreSailME ue α' β) where
  coe := e.map_error (fun x => match x with | .inl e => .inl e | .inr e => .inr e)
-/


/-
instance : Inhabited (PreSail.SequentialState RT trivialChoiceSource) where
  default := ⟨default, (), default, default, default, default⟩
-/

end SailME

end PreSail

/- CR clang: is this even used? -/
abbrev ExceptM α := ExceptT α Id

def ExceptM.run (m : ExceptM α α) : α :=
  match (ExceptT.run m) with
    | .error e => e
    | .ok e => e

namespace Sail.ConcurrencyInterfaceV1

open PreSail

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

def main_of_sail_main (initialState : SequentialState RegisterType trivialChoiceSource)
    (main : Unit → PreSailM RegisterType trivialChoiceSource ue Unit) : IO UInt32 := do
  let res := main () |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

end Sail.ConcurrencyInterfaceV1

def whileFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      if ←cond x then go (←f x) n else pure x
  go init fuel

def untilFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      let x ← f x
      if ←cond x then pure x else go x n
  go init fuel


instance : CoeT Int x Nat where
  coe := x.toNat

instance : CoeT (BitVec n) x (BitVec m) where
  coe := x.setWidth m

instance: CoeT (Vector (BitVec n₁) m) x (Vector (BitVec n₂) m) where
  coe := x.map fun (bv : BitVec n₁) => bv.setWidth n₂

instance {α α' β : Type u} (x : α × β) [CoeT α x.1 α'] : CoeT (α × β) x (α' × β) where
  coe := (x.1, x.2)

instance {α α' β : Type u} (x : β × α) [CoeT α x.2 α'] : CoeT (β × α) x (β × α') where
  coe := (x.1, x.2)

instance {α α' β β' : Type u} (x : α × β) [CoeT α x.1 α'] [CoeT β x.2 β'] : CoeT (α × β) x (α' × β') where
  coe := (x.1, x.2)

instance {α α' : Type u} [∀ x, CoeT α x α'] (xs : List α) : CoeT (List α) xs (List α') where
  coe := List.map (α := α) (β := α') (fun x => x) xs

instance (priority := low) : HAdd (BitVec n) (BitVec m) (BitVec n) where
  hAdd x y := x + y

instance (priority := low) : HSub (BitVec n) (BitVec m) (BitVec n) where
  hSub x y := x - y

instance (priority := low) : HAnd (BitVec n) (BitVec m) (BitVec n) where
  hAnd x y := x &&& y

instance (priority := low) : HOr (BitVec n) (BitVec m) (BitVec n) where
  hOr x y := x ||| y

instance (priority := low) : HXor (BitVec n) (BitVec m) (BitVec n) where
  hXor x y := x ^^^ y

instance [GetElem? coll Nat elem valid] : GetElem? coll Int elem (λ c i ↦ valid c i.toNat) where
  getElem c i h := c[i.toNat]'h
  getElem? c i := c[i.toNat]?

instance : HPow Int Int Int where
  hPow x n := x ^ n.toNat

infixl:65 " +i "   => fun (x y : Int) => x + y
infixl:65 " -i "   => fun (x y : Int) => x - y
infixl:65 " ^i "   => fun (x y : Int) => x ^ y
infixl:65 " *i "   => fun (x y : Int) => x * y

notation:50 x "≤b" y => decide (x ≤ y)
notation:50 x "<b" y => decide (x < y)
notation:50 x "≥b" y => decide (x ≥ y)
notation:50 x ">b" y => decide (x > y)

-- for termination measures, since they're almost always `Int`s but not always
abbrev Nat.toNat (x : Nat) := x

set_option grind.warning false
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)

-- This lemma replaces `bif` by `if` in functions when Lean is trying to prove
-- termination.
@[wf_preprocess]
theorem cond_eq_ite (b : Bool) (x y : α) : cond b x y = ite b x y := by cases b <;> rfl
