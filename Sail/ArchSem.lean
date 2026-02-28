import Sail.Common

namespace Sail.ArchSem

open Sail (Result)

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


/- CR clang: I would like to use lean naming convention but this conflicts with sail. -/
/- CR clang: previously in `namespace Sail.ArchSem` -/
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

/-
 - CR clang: leave commend explaining difference between sail and presail,
 - maybe namespaces generally
 -/

/- CR clang: rename n, nt -/
structure Mem_request (n : Nat) (nt : Nat) (addr_size : Nat) (addr_space : Type) (mem_acc : Type) where
  access_kind : mem_acc
  address : BitVec addr_size
  address_space : addr_space
  size : Nat
  num_tag : Nat

/- CR clang: give ue a more descriptive var name 'userError'. -/
abbrev PreSailM (ue : Type) := FreeM (Result InstructionEffect (Sail.Error ue)) (fun | .Ok eff => eff.ret | .Err _ => Empty)

abbrev PreSailME ue exception := FreeM (Result (Result InstructionEffect (Sail.Error ue)) exception)
  (fun | .Ok (.Ok eff) => eff.ret | .Ok (.Err _) => Empty | _ => Empty)

instance: MonadExcept ue (PreSailME ue α) where
  throw e := .impure (.Ok (.Err (.User e))) Empty.elim
  tryCatch eff h :=
    let rec tryCatch eff h :=
      match eff with
        | .pure v => .pure v
        | .impure (.Ok (.Err (.User err))) _cont => h err
        | .impure eff cont => .impure eff (fun v => tryCatch (cont v) h)
    tryCatch eff h

namespace PreSail

open _root_.Sail (Result)
open ArchSem
open Sail.ArchSem

variable [Arch]

inductive RegisterRef : Type → Type where
  | Reg (r : Arch.register) : RegisterRef (Arch.register_type r)
export RegisterRef (Reg)

@[simp_sail]
def sailTryCatch (e : PreSailM ue α) (h : ue → PreSailM ue α) : PreSailM ue α :=
  match e with
  | .pure v => .pure v
  | .impure (.Err (.User e)) _cont => h e
  | .impure eff cont => .impure eff (fun v => sailTryCatch (cont v) h)

@[simp_sail]
def sailThrow (e : ue) : PreSailM ue α := .impure (.Err (.User e)) Empty.elim

instance: MonadExceptOf (Sail.Error userError) (PreSailM userError) where
  throw e := FreeM.impure (.Err e) Empty.elim
  tryCatch eff h :=
    let rec tryCatch eff h := match eff with
    | .pure v => .pure v
    | .impure (.Err e) _cont => h e
    | .impure (.Ok eff) cont => .impure (.Ok eff) (fun v => tryCatch (cont v) h)
  tryCatch eff h

def choose_fin (n : Nat) : PreSailM ue (Fin n) :=
  FreeM.impure (Result.Ok (InstructionEffect.choice n)) FreeM.pure

def undefined_unit (_ : Unit) : PreSailM ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM ue (BitVec 1) := do
  return BitVec.ofFin (← choose_fin 2)

def undefined_bool (_ : Unit) : PreSailM ue Bool := do
  return ((← choose_fin 2) == 0)

def undefined_range (low high : Int) : PreSailM ue Int := do
  return (low + (← choose_fin (high - low).toNat))

def undefined_bitvector (n : Nat) : PreSailM ue (BitVec n) := do
  return @BitVec.ofFin n (← choose_fin _)

def internal_pick {α : Type} (l : List α) : PreSailM ue α := do
  if l.isEmpty then
    /-
     - CR clang for thibaut: We have discussed this before, but when I came to make
     - a change here, I realised that I still dont really understand. You told me
     - that I should not throw Unreachable here. But then I'm not really sure what
     - I can do? I need to produce a `PreSailM ue α`, but I have nowhere to get an α
     - from, so I kind of need to use an Empty.elim. And I can only do that if I have
     - an empty which I can only get by throwing some kind of error?
     -
     - The old state monad implementation was throwing unreachable:
     - https://github.com/rems-project/lean-sail/blob/aed25177482c50db6a7d8da8144388cc69da10f2/Sail/Sail.lean#L518
     -/
    .impure (.Err .Unreachable) Empty.elim
  else
    return l.get (← choose_fin l.length)

@[simp_sail]
def writeReg (r : Arch.register) (v : Arch.register_type r) : PreSailM ue PUnit :=
  FreeM.impure (Result.Ok (InstructionEffect.regWrite r Option.none v)) FreeM.pure

@[simp_sail]
def readReg (r : Arch.register) : PreSailM ue (Arch.register_type r) :=
  FreeM.impure (Result.Ok (InstructionEffect.regRead r Option.none)) FreeM.pure

@[simp_sail]
def readRegRef (reg_ref : RegisterRef α) : PreSailM ue α :=
  let .Reg r := reg_ref
  readReg r

@[simp_sail]
def writeRegRef (reg_ref : RegisterRef α) (v : α) : PreSailM ue Unit :=
  let .Reg r := reg_ref
  writeReg r v

@[simp_sail]
def reg_deref (reg_ref : RegisterRef α) : PreSailM ue α :=
  readRegRef reg_ref

@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM ue Unit :=
  if p then .pure () else .impure (.Err (.Assertion s)) Empty.elim

/- CR clang: put these utility functions somewhere better, maybe Common.lean -/
def vecbytes_to_bitvec (vec : Vector (BitVec 8) n) : BitVec (8 * n) :=
  vec.foldl (fun (i, acc) x => (i+1, Sail.BitVec.updateSubrange' acc n 8 x)) (0, BitVec.zero (8 * n))
  |> Prod.snd
def bitvec_to_vecbytes (bitvec : BitVec (8 * n)) : Vector (BitVec 8) n :=
  Vector.ofFn (fun i => Sail.BitVec.slice bitvec (8 * i) 8)
def vecbool_to_bitvec (vec : Vector Bool n) : BitVec n :=
  vec.foldl (fun (i, acc) b => (i+1, Sail.BitVec.updateSubrange' acc n 1 (BitVec.ofBool b))) (0, BitVec.zero n)
  |> Prod.snd
def bitvec_to_vecbool (bitvec : BitVec n) : Vector Bool n :=
  Vector.ofFn (fun i => BitVec.getLsb bitvec i)

def sail_mem_request_to_archsem (mem_req : Mem_request size num_tag Arch.addr_size Arch.addr_space Arch.mem_acc) : ArchSem.MemRequest :=
    { accessKind := mem_req.access_kind
    , address := mem_req.address
    , addressSpace := mem_req.address_space
    , size := size
    , numTag := num_tag }

@[simp_sail]
def sail_mem_read [Arch] (mem_req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    PreSailM ue (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) :=
  let req := sail_mem_request_to_archsem mem_req
  /- CR clang: there must be a cleaner way to write this -/
  have h : (req.size = n) ∧ (req.numTag = nt) := by
    simp [req, sail_mem_request_to_archsem]
  FreeM.impure (.Ok (InstructionEffect.memRead req))
    (FreeM.pure ∘ Result.map (fun (bytes,tags) =>
      (bitvec_to_vecbytes (And.left h ▸ bytes), bitvec_to_vecbool (And.right h ▸ tags))))

/- CR clang: why does this return an option bool. I just set to none always. -/
def sail_mem_write [Arch] (mem_req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) (valueBytes : Vector (BitVec 8) n) (tags : Vector Bool nt) :
    PreSailM ue (Result (Option Bool) Arch.abort) :=
  let req := sail_mem_request_to_archsem mem_req
  have h : (req.size = n) ∧ (req.numTag = nt) := by
    simp [req, sail_mem_request_to_archsem]
  FreeM.impure (.Ok (InstructionEffect.memWrite req
    (vecbytes_to_bitvec (And.left h ▸ valueBytes)) (vecbool_to_bitvec (And.right h ▸ tags))))
    (fun | .Ok () => .pure (.Ok .none) | .Err e => .pure (.Err e))

@[simp_sail]
def sail_sys_reg_read [Arch] (_id : Arch.sys_reg_id) (r : RegisterRef α) : PreSailM ue α :=
  readRegRef r

@[simp_sail]
def sail_sys_reg_write [Arch] (_id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : PreSailM ue Unit :=
  writeRegRef r v

def sail_mem_address_announce [Arch] (_ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) : PreSailM ue Unit :=
  pure ()

@[simp_sail]
def sail_translation_start [Arch] (_ : Arch.trans_start) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_translation_end [Arch] (_ : Arch.trans_end) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_barrier [Arch] (_ : Arch.barrier) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_take_exception [Arch] (_ : Arch.exn) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_return_exception (_ : Unit) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_cache_op [Arch] (_ : Arch.cache_op) : PreSailM ue Unit := pure ()

@[simp_sail]
def sail_tlbi [Arch] (_ : Arch.tlbi) : PreSailM ue Unit := pure ()

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM ue Unit :=
  .impure (.Ok (.clockCycle)) .pure

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM ue Nat := do
  .impure (.Ok (.getCycleCount)) .pure

def print_effect (str : String) : PreSailM ue Unit :=
  .impure (.Ok (.printMessage str)) .pure

def print_int_effect (str : String) (n : Int) : PreSailM ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM ue Unit :=
  print_effect s!"{str}{Sail.BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM ue Unit :=
  print_effect s!"{str}\n"

/-
 - CR clang: this is here for compatability with Out/Specialization.lean in the generated isa spec.
 - I've just duplicated the above tryCatch func.
 -/
def sailTryCatchE (eff : PreSailME ue e α) (h : ue → PreSailME ue e α) : PreSailME ue e α :=
  match eff with
    | .pure v => .pure v
    | .impure (.Ok (.Err (.User err))) _cont => h err
    | .impure eff cont => .impure eff (fun v => tryCatch (cont v) h)

def PreSailME.run : PreSailME ue α α → PreSailM ue α
 | .pure v => .pure v
 | .impure (.Err ret) _cont => .pure ret
 | .impure (.Ok eff) cont => .impure eff (fun v => PreSailME.run (cont (cast (by split <;> rfl) v)))

def PreSailME.throw (e : α) : PreSailME ue α β :=
  .impure (.Err e) Empty.elim

instance : MonadLift (PreSailM ue) (PreSailME ue ε) where
  monadLift m :=
    let rec lift m :=
      match m with
      | .pure v => .pure v
      | .impure eff cont => .impure (.Ok eff) (fun v => lift (cont (cast (by symm ; split <;> rfl) v)))
    lift m

end Sail.ArchSem.PreSail
