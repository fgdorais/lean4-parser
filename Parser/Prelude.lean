import Std
import UnicodeData

structure ByteSubarray extends ByteArray where
  start : Nat
  size  : Nat
  valid : start + size ≤ toByteArray.size := by simp_arith [*]

abbrev ByteSubarray.stop (bs : ByteSubarray) : Nat := bs.start + bs.size

def ByteArray.toByteSubarray (bs : ByteArray) : ByteSubarray where
  toByteArray := bs
  start := 0
  size := bs.size

namespace ByteSubarray
variable (bs : ByteSubarray)

@[inline] def extract : ByteArray := bs.toByteArray.extract bs.start bs.stop

@[inline] def get (i : Fin bs.size) : UInt8 :=
  have : bs.start + i.val < bs.toByteArray.size := calc
    _ < bs.start + bs.size := Nat.add_lt_add_left i.isLt bs.start
    _ ≤ bs.toByteArray.size := bs.valid
  bs.toByteArray[bs.start + i.val]'this

instance : GetElem ByteSubarray Nat UInt8 fun bs i => i < bs.size where
  getElem xs i h := xs.get ⟨i, h⟩

@[inline] def get? (i : Nat) : Option UInt8 :=
  if h : i < bs.size then some (bs.get ⟨i, h⟩) else none

@[inline] def getD (i : Nat) (default : UInt8) : UInt8 :=
  if h : i < bs.size then bs.get ⟨i, h⟩ else default

abbrev get! (i : Nat) : UInt8 := getD bs i default

def popFront : ByteSubarray :=
  if h : bs.size ≥ 1 then
    have : (bs.start+1) + (bs.size-1) = bs.start + bs.size := by
      rw [Nat.add_assoc, Nat.add_sub_cancel' h]
    {bs with start := bs.start+1, size := bs.size-1, valid := by rw [this]; exact bs.valid}
  else bs

def slice (start stop : Nat) (h : start ≤ stop ∧ stop ≤ bs.size := by simp_arith [*]) : ByteSubarray where
  toByteArray := bs.toByteArray
  start := bs.start + start
  size := stop - start
  valid := by
    rw [Nat.add_assoc]
    rw [Nat.add_sub_cancel' h.1]
    apply Nat.le_trans _ bs.valid
    apply Nat.add_le_add_left h.2

@[simp] theorem size_slice (start stop : Nat) (h : start ≤ stop ∧ stop ≤ bs.size := by simp_arith [*]) : (bs.slice start stop h).size = stop - start := rfl

@[inline] unsafe def forInUnsafe {α m} [Monad m] (bs : ByteSubarray) (a : α) (f : UInt8 → α → m (ForInStep α)) : m α :=
  let sz := USize.ofNat bs.stop
  let rec @[specialize] loop (i : USize) (a : α) : m α := do
    if i < sz then
      let b := bs.uget i lcProof
      match (← f b a) with
      | ForInStep.done  a => pure a
      | ForInStep.yield a => loop (i+1) a
    else
      pure a
  loop (USize.ofNat bs.start) a

@[implemented_by ByteSubarray.forInUnsafe]
protected def forIn {α m} [Monad m] (bs : ByteSubarray) (a : α) (f : UInt8 → α → m (ForInStep α)) : m α :=
  let rec @[specialize] loop (i : Nat) (a : α) : m α := do
    if h : i < bs.size then
      let b := bs.get ⟨i, h⟩
      match (← f b a) with
      | ForInStep.done  a => pure a
      | ForInStep.yield a => loop (i+1) a
    else
      pure a
  loop bs.start a
termination_by loop => bs.size - i

instance : ForIn m ByteSubarray UInt8 where
  forIn := ByteSubarray.forIn

instance : Stream ByteSubarray UInt8 where
  next? s :=
    if h : s.size > 0 then
      some (s.get ⟨0, h⟩, s.popFront)
    else
      none

end ByteSubarray
