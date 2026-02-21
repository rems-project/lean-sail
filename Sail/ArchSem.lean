namespace ArchSem

/- CR clang: Previously in `namespace Sail` -/
inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

def Result.map (f: α → β) (r : Result α ε) : Result β ε := match r with
| Result.Ok v => Result.Ok (f v)
| Result.Err e => Result.Err e

inductive FreeM.{u, v, w} (Eff : Type v) (eff_ret : Eff → Type u) (α : Type w) where
  | pure (a : α) : FreeM Eff eff_ret α
  | impure (call : Eff) (cont : eff_ret call → FreeM Eff eff_ret α) : FreeM Eff eff_ret α

def FreeM.bind (x : FreeM Eff effRet α) (f : α → FreeM Eff effRet β) : FreeM Eff effRet β :=
  match x with
    | FreeM.pure x => f x
    | FreeM.impure op cont => FreeM.impure op (fun r => FreeM.bind (cont r) f)

instance : Monad (FreeM Eff effRet) where
  pure x := FreeM.pure x
  bind := FreeM.bind

/- CR clang: Previously in `namespace Sail` -/
inductive Primitive where
  | bool
  | bit
  | int
  | nat
  | string
  | fin (n : Nat)
  | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | bool => Bool
  | bit => BitVec 1
  | int => Int
  | nat => Nat
  | string => String
  | fin n => Fin (n + 1)
  | bitvector n => BitVec n

/- CR clang: I would like to use lean naming convention but this conflicts with sail. -/
/- CR clang: previously in `namespace Sail.ConcurrencyInterfaceV2` -/
/- CR clang: Add some comments explaining the fields of Arch. -/
class Arch where
  addr_size : Nat
  addr_space : Type
  CHERI : Bool
  cap_size_log : Nat
  register : Type
  register_type : register → Type
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

variable [Arch]

/- CR clang: leave a comment here explaining different MemRequest structures. -/
structure MemRequest where
  accessKind : Arch.mem_acc
  address : BitVec Arch.addr_size
  addressSpace : Arch.addr_space
  size : Nat
  numTag : Nat

/- CR clang: See rocq-lean effects in ArchSem/Interface.v `outcome` -/
/- CR clang: After discussion with Thibaut on Mon 26th Jan: We are going to make
this inductive type take an `Error : type` argument. Then this will be instantiated
something like :
  PreSailM : FrMon (outcome arch (generic_error + user_error))
  PreArchM : FreeMon (outcome (generic_error))
  PreSailME : Free Mon(outcome (generic error + user error + A:type))
-/
inductive InstructionEffect where
  | regRead (reg : Arch.register) (accessType : Option Arch.sys_reg_id)
  | regWrite (reg : Arch.register) (accessType : Option Arch.sys_reg_id) (value: Arch.register_type reg)
  | memRead (memReq : MemRequest)
  | memWrite (memReq : MemRequest) (value : BitVec (8 * memReq.size)) (tags : BitVec (memReq.numTag))
  | memWriteAnnounce (memReq : MemRequest)
  | barrier (barrier : Arch.barrier)
  | cacheOp (op : Arch.cache_op)
  | tlbOp (op : Arch.tlbi)
  /- | choice (primitive : Primitive) -/
  | choice (n : Nat)
  | clockCycle
  | getCycleCount
  | translationStart (translationStart : Arch.trans_start)
  | translationEnd (translationEnd : Arch.trans_end)
  | archException (exception : Arch.exn)
  | returnExecption
  /- CR clang: Maybe split this out into different types: -/
  | printMessage (msg : String)

/- CR clang: namespcae this -/
def InstructionEffect.ret : InstructionEffect → Type
  | .regRead reg _ => Arch.register_type reg
  | .regWrite _ _ _ => Unit
  | .memRead memReq => Result (BitVec (8 * memReq.size) × BitVec (memReq.numTag)) Arch.abort
  | .memWrite _ _ _ => Result Unit Arch.abort
  | .memWriteAnnounce _ => Unit
  | .barrier _ => Unit
  | .cacheOp _ => Unit
  | .tlbOp _ => Unit
  /- | .choice primitive => primitive.reflect -/
  | .choice n => Fin n
  | .clockCycle => Unit
  | .getCycleCount => Nat
  | .translationStart _ => Unit
  | .translationEnd _ => Unit
  | .archException _ => Unit
  | .returnExecption => Unit
  | .printMessage _ => Unit

end ArchSem
