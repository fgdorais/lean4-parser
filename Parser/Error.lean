/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Stream

/-- Parser error class -/
protected class Parser.Error (ε σ : Type _) (α : outParam (Type _)) [Parser.Stream σ α] where
  /-- Unexpected input -/
  unexpected : Stream.Position σ → Option α → ε
  /-- Add error message -/
  addMessage : ε → Stream.Position σ → String → ε

namespace Parser.Error

/-- Trivial error type -/
abbrev Trivial := Unit

instance (σ α) [Parser.Stream σ α] : Parser.Error Trivial σ α where
  unexpected _ _ := ()
  addMessage e _ _ := e

/-- Basic error type -/
abbrev Basic (σ α) [Parser.Stream σ α] := Parser.Stream.Position σ × Option α

instance (σ α) [Parser.Stream σ α] : Parser.Error (Basic σ α) σ α where
  unexpected p t := (p, t)
  addMessage e _ _ := e

instance (σ α) [Repr α] [Parser.Stream σ α] [Repr (Parser.Stream.Position σ)] : ToString (Basic σ α) where
  toString
    | (pos, some tok) => s!"unexpected input {repr tok} at {repr pos}"
    | (pos, none) => s!"unexpected input at {repr pos}"

/-- Simple error type -/
inductive Simple (σ α) [Parser.Stream σ α]
  /-- Unexpected token at position -/
  | unexpected : Stream.Position σ → Option α → Simple σ α
  /-- Add error message at position -/
  | addMessage : Simple σ α → Stream.Position σ → String → Simple σ α

-- The derive handler for `Repr` fails, this is a workaround.
private def Simple.reprPrec {σ α} [Parser.Stream σ α] [Repr α] [Repr (Stream.Position σ)] : Simple σ α → Nat → Std.Format
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

instance (σ α) [Parser.Stream σ α] [Repr α] [Repr (Stream.Position σ)] : Repr (Simple σ α) where
  reprPrec := Simple.reprPrec

private def Simple.toString {σ α} [Repr α] [Parser.Stream σ α] [Repr (Parser.Stream.Position σ)] : Simple σ α → String
  | unexpected pos (some tok) => s!"unexpected token {repr tok} at {repr pos}"
  | unexpected pos none => s!"unexpected token at {repr pos}"
  | addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {repr pos}"

instance (σ α) [Repr α] [Parser.Stream σ α] [Repr (Parser.Stream.Position σ)] : ToString (Simple σ α) where
  toString := Simple.toString

instance (σ α) [Parser.Stream σ α] : Parser.Error (Simple σ α) σ α where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error
