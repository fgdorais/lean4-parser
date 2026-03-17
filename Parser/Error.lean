/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Prelude
import Parser.Stream

/-! # Parser Error

The class `Parser.Error` is used throughout the library for the purpose of reporting parser errors.
Users are encouraged to provide their own instances tailored to their applications.

Three general purpose instances are provided:

* `Parser.Error.Simple` records all parsing error information, without processing.
* `Parser.Error.Basic` just records the location of the primary parsing error.
* `Parser.Error.Trivial` discards all parsing error information.

These are intended for use in parser development and as building blocks (or inspiration) for
tailored instances.
-/

/-- *Parser error class*

This class declares an error type for a given parser stream.

Given `Parser.Stream σ τ`, `Parser.Error ε σ τ` provides two basic mechanisms for reporting parsing
errors:

* `unexpected {s : σ} (p : Stream.Position s) (t : Option τ) : ε`
  is used to report an unexpected input at a given position, optionally with the offending token.
* `addMessage {s : σ} (e : ε) (p : Stream.Position s) (info : String)`
  is used to add additional error information at a given position.

This class can be extended to provide additional error reporting and processing functonality, but
only these two mechanisms are used within the library.
-/
protected class Parser.Error (ε σ : Type _) (τ : outParam (Type _)) [Parser.Stream σ τ] where
  unexpected {s : σ}: Stream.Position s → Option τ → ε
  addMessage {s : σ} : ε → Stream.Position s → String → ε
attribute [inherit_doc Parser.Error] Parser.Error.unexpected Parser.Error.addMessage

namespace Parser.Error

/-- *Trivial error type*

This error type simply discards all error information. This is useful for parsers that cannot fail,
or where parsing errors are intended to be handled by other means.
-/
abbrev Trivial := Unit

instance (σ τ) [Parser.Stream σ τ] : Parser.Error Trivial σ τ where
  unexpected _ _ := ()
  addMessage e _ _ := e

/-- *Basic error type*

This error type records the position and, optionally, the offending token where a parsing error
occurred; any additional information is discarded. This is useful for parsers where the cause of
parsing errors is predictable and only the position of the error is needed for processing.
-/
abbrev Basic (σ τ) [Parser.Stream σ τ] := (s : σ) × Parser.Stream.Position s × Option τ

instance (τ) [Parser.Stream σ τ] : Parser.Error (Basic σ τ) σ τ where
  unexpected p t := ⟨_, p, t⟩
  addMessage e _ _ := e

instance (σ τ) [Repr τ] [Parser.Stream σ τ] [(s : σ) → Repr (Parser.Stream.Position s)] :
  ToString (Basic σ τ) where
  toString
    | ⟨_, pos, some tok⟩ => s!"unexpected input {repr tok} at {repr pos}"
    | ⟨_, pos, none⟩ => s!"unexpected input at {repr pos}"

/-- *Simple error type*

This error type simply records all the error information provided, without additional processing.
Users are expected to provide any necessary post-processing. This is useful for parser development.
-/
inductive Simple (σ τ) [Parser.Stream σ τ]
  /-- Unexpected input at position -/
  | unexpected {s : σ} : Stream.Position s → Option τ → Simple σ τ
  /-- Add error message at position -/
  | addMessage {s : σ} : Simple σ τ → Stream.Position s → String → Simple σ τ

-- The derive handler for `Repr` fails, this is a workaround.
private def Simple.reprPrec {σ τ} [Parser.Stream σ τ] [Repr τ] [(s : σ) → Repr (Stream.Position s)] :
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

instance (σ τ) [Parser.Stream σ τ] [Repr τ] [(s : σ) → Repr (Stream.Position s)] : Repr (Simple σ τ) where
  reprPrec := Simple.reprPrec

private def Simple.toString {σ τ} [Repr τ] [Parser.Stream σ τ] [(s : σ) → ToString (Parser.Stream.Position s)] :
  Simple σ τ → String
  | unexpected pos (some tok) => s!"unexpected token {repr tok} at {pos}"
  | unexpected pos none => s!"unexpected token at {pos}"
  | addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {pos}"

instance (σ τ) [Repr τ] [Parser.Stream σ τ] [(s : σ) → ToString (Parser.Stream.Position s)] :
  ToString (Simple σ τ) where
  toString := Simple.toString

instance (σ τ) [Parser.Stream σ τ] : Parser.Error (Simple σ τ) σ τ where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error
