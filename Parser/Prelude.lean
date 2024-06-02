/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Batteries
import UnicodeBasic

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

@[inline]
def extract (bs : ByteSubarray) : ByteArray := bs.toByteArray.extract bs.start bs.stop

@[inline]
def get (bs : ByteSubarray) (i : Fin bs.size) : UInt8 :=
  have : bs.start + i.val < bs.toByteArray.size := calc
    _ < bs.start + bs.size := Nat.add_lt_add_left i.isLt bs.start
    _ ≤ bs.toByteArray.size := bs.valid
  bs.toByteArray[bs.start + i.val]

instance : GetElem ByteSubarray Nat UInt8 fun bs i => i < bs.size where
  getElem xs i h := xs.get ⟨i, h⟩

@[inline]
def get? (bs : ByteSubarray) (i : Nat) : Option UInt8 :=
  if h : i < bs.size then some (bs.get ⟨i, h⟩) else none

@[inline]
def getD (bs : ByteSubarray) (i : Nat) (default : UInt8) : UInt8 :=
  if h : i < bs.size then bs.get ⟨i, h⟩ else default

abbrev get! (bs : ByteSubarray) (i : Nat) : UInt8 := getD bs i default

def popFront (bs : ByteSubarray) : ByteSubarray :=
  if h : bs.size ≥ 1 then
    have : (bs.start+1) + (bs.size-1) = bs.start + bs.size := by
      rw [Nat.add_assoc, Nat.add_sub_cancel' h]
    {bs with start := bs.start+1, size := bs.size-1, valid := by rw [this]; exact bs.valid}
  else bs

def slice (bs : ByteSubarray) (start stop : Nat) (h : start ≤ stop ∧ stop ≤ bs.size := by simp_arith [*]) : ByteSubarray where
  toByteArray := bs.toByteArray
  start := bs.start + start
  size := stop - start
  valid := by
    rw [Nat.add_assoc]
    rw [Nat.add_sub_cancel' h.1]
    apply Nat.le_trans _ bs.valid
    apply Nat.add_le_add_left h.2

@[simp]
theorem size_slice (bs : ByteSubarray) (start stop : Nat) (h : start ≤ stop ∧ stop ≤ bs.size := by simp_arith [*]) : (bs.slice start stop h).size = stop - start := rfl

@[inline]
unsafe def forInUnsafe {τ m} [Monad m] (bs : ByteSubarray) (a : τ) (f : UInt8 → τ → m (ForInStep τ)) : m τ :=
  loop (USize.ofNat bs.start) a
where
  @[specialize]
  loop (i : USize) (a : τ) : m τ := do
    if i < USize.ofNat bs.stop then
      let b := bs.uget i lcProof
      match (← f b a) with
      | ForInStep.done  a => pure a
      | ForInStep.yield a => loop (i+1) a
    else
      pure a

@[implemented_by ByteSubarray.forInUnsafe]
protected def forIn {τ m} [Monad m] (bs : ByteSubarray) (a : τ) (f : UInt8 → τ → m (ForInStep τ)) : m τ :=
  loop bs.start a
where
  loop (i : Nat) (a : τ) : m τ := do
    if h : i < bs.size then
      let b := bs.get ⟨i, h⟩
      match (← f b a) with
      | ForInStep.done  a => pure a
      | ForInStep.yield a => loop (i+1) a
    else
      pure a
termination_by bs.size - i

instance : ForIn m ByteSubarray UInt8 where
  forIn := ByteSubarray.forIn

instance : Stream ByteSubarray UInt8 where
  next? s :=
    if h : s.size > 0 then
      some (s.get ⟨0, h⟩, s.popFront)
    else
      none

end ByteSubarray
