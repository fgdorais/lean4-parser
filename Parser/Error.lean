/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Stream

/-- Parser error class -/
protected class Parser.Error (ε σ : Type _) (τ : outParam (Type _)) [Parser.Stream σ τ] where
  /-- Unexpected input -/
  unexpected : Stream.Position σ → Option τ → ε
  /-- Add error message -/
  addMessage : ε → Stream.Position σ → String → ε

namespace Parser.Error

/-- Trivial error type -/
abbrev Trivial := Unit

instance (σ τ) [Parser.Stream σ τ] : Parser.Error Trivial σ τ where
  unexpected _ _ := ()
  addMessage e _ _ := e

/-- Basic error type -/
abbrev Basic (σ τ) [Parser.Stream σ τ] := Parser.Stream.Position σ × Option τ

instance (σ τ) [Parser.Stream σ τ] : Parser.Error (Basic σ τ) σ τ where
  unexpected p t := (p, t)
  addMessage e _ _ := e

instance (σ τ) [Repr τ] [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] :
  ToString (Basic σ τ) where
  toString
    | (pos, some tok) => s!"unexpected input {repr tok} at {repr pos}"
    | (pos, none) => s!"unexpected input at {repr pos}"

/-- Simple error type -/
inductive Simple (σ τ) [Parser.Stream σ τ]
  /-- Unexpected token at position -/
  | unexpected : Stream.Position σ → Option τ → Simple σ τ
  /-- Add error message at position -/
  | addMessage : Simple σ τ → Stream.Position σ → String → Simple σ τ

-- The derive handler for `Repr` fails, this is a workaround.
private def Simple.reprPrec {σ τ} [Parser.Stream σ τ] [Repr τ] [Repr (Stream.Position σ)] :
  Simple σ τ → Nat → Std.Format
  | unexpected pos a, prec =>
    Repr.addAppParen
      (Std.Format.group
        (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.text "Parser.Error.Simple.unexpected" ++
            Std.Format.line ++
            reprArg pos ++
            Std.Format.line ++
            reprArg a)))
      prec
  | addMessage e pos msg, prec =>
    Repr.addAppParen
      (Std.Format.group
        (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.text "Parser.Error.Simple.addMessage" ++
            Std.Format.line ++
            reprPrec e max_prec ++
            Std.Format.line ++
            reprArg pos ++
            Std.Format.line ++
          reprArg msg)))
      prec

instance (σ τ) [Parser.Stream σ τ] [Repr τ] [Repr (Stream.Position σ)] : Repr (Simple σ τ) where
  reprPrec := Simple.reprPrec

private def Simple.toString {σ τ} [Repr τ] [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] :
  Simple σ τ → String
  | unexpected pos (some tok) => s!"unexpected token {repr tok} at {repr pos}"
  | unexpected pos none => s!"unexpected token at {repr pos}"
  | addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {repr pos}"

instance (σ τ) [Repr τ] [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] :
  ToString (Simple σ τ) where
  toString := Simple.toString

instance (σ τ) [Parser.Stream σ τ] : Parser.Error (Simple σ τ) σ τ where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error
