/-
Copyright © 2022-2023 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Basic
import Parser.Char.Basic

namespace Parser.Char.ASCII
variable {ε σ m} [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] [MonadExceptOf ε m]

@[inline]
private def decNum (n : Nat := 0) : ParserT ε σ Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 10) => (10 * r.1 + d, r.2+1)) (pure (n,0)) ASCII.digit

@[inline]
private def binNum (n : Nat := 0) : ParserT ε σ Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 2) => (r.1 <<< 1 + d, r.2+1)) (pure (n,0)) ASCII.binDigit

@[inline]
private def octNum (n : Nat := 0) : ParserT ε σ Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 8) => (r.1 <<< 3 + d, r.2+1)) (pure (n,0)) ASCII.octDigit

@[inline]
private def hexNum (n : Nat := 0) : ParserT ε σ Char m (Nat × Nat) :=
  foldl (fun (r : Nat × Nat) (d : Fin 16) => (r.1 <<< 4 + d, r.2+1)) (pure (n,0)) ASCII.hexDigit

/-- Parse a `Nat` -/
def parseNat (decimalOnly := true) : ParserT ε σ Char m Nat := do
  match ← ASCII.digit with
  | ⟨0, _⟩ =>
    if decimalOnly then
      Prod.fst <$> ASCII.decNum
    else
      first [
        char 'b' *> binNum,
        char 'x' *> hexNum,
        octNum,
        return 0]
  | ⟨n, _⟩ => Prod.fst <$> ASCII.decNum n
where
  binNum := do
    let ⟨n, _⟩ ← ASCII.binDigit
    Prod.fst <$> ASCII.binNum n
  octNum := do
    let ⟨n, _⟩ ← ASCII.octDigit
    Prod.fst <$> ASCII.octNum n
  hexNum := do
    let ⟨n, _⟩ ← ASCII.hexDigit
    Prod.fst <$> ASCII.hexNum n

/-- Parse an `Int` -/
def parseInt (decimalOnly := true) : ParserT ε σ Char m Int := do
  match ← option? (char '+' <|> char '-') with
  | some '-' => Int.negOfNat <$> parseNat decimalOnly
  | _ => Int.ofNat <$> parseNat decimalOnly

/-- Parse scientific notation -/
@[inline]
def parseScientific (α) [OfScientific α] : ParserT ε σ Char m α := do
  let (man, pre) ← ASCII.decNum
  let (man, aft) ← (char '.' *> ASCII.decNum man) <|> pure (man, 0)
  if pre + aft = 0 then throwUnexpected
  let exp : Int ← ((char 'E' <|> char 'e') *> parseInt) <|> pure 0
  return OfScientific.ofScientific man (exp < aft) (exp - aft).natAbs

/-- Parse a `Float` -/
def parseFloat : ParserT ε σ Char m Float := do
  match ← option? (char '+' <|> char '-') with
  | some '-' => Float.neg <$> parseScientific Float
  | _ => parseScientific Float

end Parser.Char.ASCII
