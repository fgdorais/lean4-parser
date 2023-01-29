import Std
import Unicode

structure ByteSubarray extends ByteArray where
  start : Nat
  stop : Nat
  sound : start ≤ stop ∧ stop ≤ toByteArray.size

def ByteArray.toByteSubarray (bs : ByteArray) : ByteSubarray where
  toByteArray := bs
  start := 0
  stop := bs.size
  sound := ⟨Nat.zero_le bs.size, Nat.le_refl bs.size⟩

namespace ByteSubarray
variable (bs : ByteSubarray)

@[inline] def extract : ByteArray := bs.toByteArray.extract bs.start bs.stop

@[inline] def size : Nat := bs.stop - bs.start

@[inline] def get (i : Fin bs.size) : UInt8 :=
  have : i.val + bs.start < bs.toByteArray.size := calc
    _ < bs.size + bs.start := Nat.add_lt_add_right i.isLt bs.start
    _ = bs.stop := Nat.sub_add_cancel bs.sound.1
    _ ≤ bs.toByteArray.size := bs.sound.2
  bs.toByteArray[i.val + bs.start]'this

instance : GetElem ByteSubarray Nat UInt8 fun bs i => i < bs.size where
  getElem xs i h := xs.get ⟨i, h⟩

@[inline] def get? (i : Nat) : Option UInt8 :=
  if h : i < bs.size then some (bs.get ⟨i, h⟩) else none

@[inline] def getD (i : Nat) (default : UInt8) : UInt8 :=
  if h : i < bs.size then bs.get ⟨i, h⟩ else default

abbrev get! (i : Nat) : UInt8 := getD bs i default

def popFront : ByteSubarray :=
  if h : bs.start < bs.stop
  then { bs with start := bs.start + 1, sound := ⟨Nat.le_of_lt_succ (Nat.add_lt_add_right h 1), bs.sound.2⟩ }
  else bs

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
    if h : s.start < s.stop
    then some (s.get ⟨0, Nat.sub_pos_of_lt h⟩, {s with start := s.start+1, sound := ⟨Nat.succ_le_of_lt h, s.sound.2⟩})
    else none

end ByteSubarray
