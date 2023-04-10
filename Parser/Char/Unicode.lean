/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser.Char.Basic

namespace Parser.Char.Unicode
variable {ε σ m} [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] [MonadExceptOf ε m]

/-- parse alphabetic letter character -/
def alpha : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter" do
    tokenFilter Unicode.isAlpha

/-- parse lowercase letter character -/
def lowercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter" do
    tokenFilter Unicode.isLowercase

/-- parse math symbol character -/
def math : ParserT ε σ Char m Char :=
  withErrorMessage "expected math symbol" do
    tokenFilter Unicode.isMath

/-- parse uppercase letter character -/
def uppercase : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter" do
    tokenFilter Unicode.isUppercase

/-- parse whitespace character -/
def whitespace : ParserT ε σ Char m Char :=
  withErrorMessage "expected whitespace" do
    tokenFilter Unicode.isWhiteSpace

/-- parse decimal digit character -/
def digit : ParserT ε σ Char m (Fin 10) :=
  withErrorMessage "expected decimal digit" do
    tokenMap Unicode.getDigit?

/-- parse hexadecimal digit character -/
def hexDigit : ParserT ε σ Char m (Fin 16) :=
  withErrorMessage "expected hexadecimal decimal digit" do
    tokenMap Unicode.getHexDigit?

/-!
  ## General Category ##
-/

/-- parse character from given general category -/
def parseGeneralCategory (category : Unicode.GeneralCategory) : ParserT ε σ Char m Char :=
  withErrorMessage s!"expected character of general category {category.toAbbrev}" do
    tokenFilter (Unicode.isInGeneralCategory . category)

namespace GeneralCategory

/-- parse letter (general category L) -/
def letter : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter (L)" do
    tokenFilter Unicode.GeneralCategory.isLetter

/-- parse cased letter (general category LC) -/
def casedLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected cased letter (LC)" do
    tokenFilter Unicode.GeneralCategory.isCasedLetter

/-- parse lowercase letter (general category Ll) -/
def lowercaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter (Ll)" do
    tokenFilter Unicode.GeneralCategory.isLowercaseLetter

/-- parse uppercase letter (general category Lu) -/
def uppercaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter (Lu)" do
    tokenFilter Unicode.GeneralCategory.isUppercaseLetter

/-- parse titlecase letter (general category Lt) -/
def titlecaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected titlecase letter (Lt)" do
    tokenFilter Unicode.GeneralCategory.isTitlecaseLetter

/-- parse other letter (general category Lm) -/
def modifierLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected modifier letter (Lm)" do
    tokenFilter Unicode.GeneralCategory.isModifierLetter

/-- parse other letter (general category Lo) -/
def otherLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected other letter (Lo)" do
    tokenFilter Unicode.GeneralCategory.isOtherLetter

/-- parse mark (general category M) -/
def mark : ParserT ε σ Char m Char :=
  withErrorMessage "expected mark (M)" do
    tokenFilter Unicode.GeneralCategory.isMark

/-- parse spacing combining mark (general category Mc) -/
def spacingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected spacing mark (Mc)" do
    tokenFilter Unicode.GeneralCategory.isSpacingMark

/-- parse nonspacing combining mark (general category Mn) -/
def nonspacingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected nonspacing mark (Mn)" do
    tokenFilter Unicode.GeneralCategory.isNonspacingMark

/-- parse enclosing combining mark (general category Me) -/
def enclosingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected enclosing mark (Me)" do
    tokenFilter Unicode.GeneralCategory.isEnclosingMark

/-- parse number (general category N) -/
def number : ParserT ε σ Char m Char :=
  withErrorMessage "expected number (N)" do
    tokenFilter Unicode.GeneralCategory.isNumber

/-- parse decimal number (general category Nd) -/
def decimalNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected decimal number (Nd)" do
    tokenFilter Unicode.GeneralCategory.isDecimalNumber

/-- parse letter number (general category Nl) -/
def letterNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter number (Nl)" do
    tokenFilter Unicode.GeneralCategory.isLetterNumber

/-- parse other number (general category No) -/
def otherNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected other number (No)" do
    tokenFilter Unicode.GeneralCategory.isOtherNumber

/-- parse punctuation (general category P) -/
def punctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected punctuation (P)" do
    tokenFilter Unicode.GeneralCategory.isPunctuation

/-- parse connector punctuation (general category Pc) -/
def connectorPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected connector punctuation (Pc)" do
    tokenFilter Unicode.GeneralCategory.isConnectorPunctuation

/-- parse dash punctuation (general category Pd) -/
def dashPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected dash punctuation (Pd)" do
    tokenFilter Unicode.GeneralCategory.isDashPunctuation

/-- parse opening punctuation (general category Ps) -/
def openPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected opening punctuation (Ps)" do
    tokenFilter Unicode.GeneralCategory.isOpenPunctuation

/-- parse closing punctuation (general category Pe) -/
def closePunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected opening punctuation (Pe)" do
    tokenFilter Unicode.GeneralCategory.isClosePunctuation

/-- parse initial punctuation (general category Pi) -/
def initialPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected initial punctuation (Pi)" do
    tokenFilter Unicode.GeneralCategory.isInitialPunctuation

/-- parse final punctuation (general category Pf) -/
def finalPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected final punctuation (Pf)" do
    tokenFilter Unicode.GeneralCategory.isFinalPunctuation

/-- parse other punctuation (general category Po) -/
def otherPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected other punctuation (Po)" do
    tokenFilter Unicode.GeneralCategory.isOtherPunctuation

/-- parse symbol (general category S) -/
def symbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected symbol (S)" do
    tokenFilter Unicode.GeneralCategory.isSymbol

/-- parse math symbol (general category Sm) -/
def mathSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected math symbol (Sm)" do
    tokenFilter Unicode.GeneralCategory.isMathSymbol

/-- parse currency symbol (general category Sc) -/
def currencySymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected currency symbol (Sc)" do
    tokenFilter Unicode.GeneralCategory.isCurrencySymbol

/-- parse modifier symbol (general category Sk) -/
def modifierSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected modifier symbol (Sk)" do
    tokenFilter Unicode.GeneralCategory.isModifierSymbol

/-- parse other symbol (general category So) -/
def otherSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected other symbol (So)" do
    tokenFilter Unicode.GeneralCategory.isOtherSymbol

/-- parse separator (general category Z) -/
def separator : ParserT ε σ Char m Char :=
  withErrorMessage "expected separator (Z)" do
    tokenFilter Unicode.GeneralCategory.isSeparator

/-- parse space separator (general category Zs) -/
def spaceSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected space separator (Zs)" do
    tokenFilter Unicode.GeneralCategory.isSpaceSeparator

/-- parse line separator (general category Zl) -/
def lineSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected line separator (Zl)" do
    tokenFilter Unicode.GeneralCategory.isLineSeparator

/-- parse paragraph separator (general category Zp) -/
def paragraphSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected paragraph separator (Zp)" do
    tokenFilter Unicode.GeneralCategory.isParagraphSeparator

/-- parse other character (general category C) -/
def other : ParserT ε σ Char m Char :=
  withErrorMessage "expected other character (C)" do
    tokenFilter Unicode.GeneralCategory.isOther

/-- parse control character (general category Cc) -/
def control : ParserT ε σ Char m Char :=
  withErrorMessage "expected control character (Cc)" do
    tokenFilter Unicode.GeneralCategory.isControl

/-- parse format character (general category Cf) -/
def format : ParserT ε σ Char m Char :=
  withErrorMessage "expected format character (Cf)" do
    tokenFilter Unicode.GeneralCategory.isFormat

/-- parse surrogate character (general category Cs) -/
def surrogate : ParserT ε σ Char m Char :=
  withErrorMessage "expected surrogate character (Cs)" do
    tokenFilter Unicode.GeneralCategory.isSurrogate

/-- parse private-use character (general category Co) -/
def privateUse : ParserT ε σ Char m Char :=
  withErrorMessage "expected private-use character (Co)" do
    tokenFilter Unicode.GeneralCategory.isPrivateUse

/-- parse unassigned character (general category Cn) -/
def noncharacter : ParserT ε σ Char m Char :=
  withErrorMessage "expected unassigned character (Cn)" do
    tokenFilter Unicode.GeneralCategory.isUnassigned

end GeneralCategory

end Parser.Char.Unicode
