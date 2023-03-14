import Parser.Char.Basic

namespace Parser.Char.Unicode
variable {ε σ m} [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m] [MonadExceptOf ε m]

/-- parse decimal digit character -/
def decimalDigit : ParserT ε σ Char m (Fin 10) :=
  withErrorMessage "expected decimal digit" do
    tokenMap Unicode.toDigit?

/- General Category -/

/-- parse character from given general category -/
def parseGeneralCategory (category : Unicode.GeneralCategory) : ParserT ε σ Char m Char :=
  withErrorMessage s!"expected character of general category {category.toAbbrev}" do
    tokenFilter (Unicode.isInGeneralCategory . category)

/-- parse letter (general category L) -/
def letter : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter (L)" do
    tokenFilter Unicode.isLetter

/-- parse cased letter (general category LC) -/
def casedLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected cased letter (LC)" do
    tokenFilter Unicode.isCasedLetter

/-- parse lowercase letter (general category Ll) -/
def lowercaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected lowercase letter (Ll)" do
    tokenFilter Unicode.isLowercaseLetter

/-- parse uppercase letter (general category Lu) -/
def uppercaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected uppercase letter (Lu)" do
    tokenFilter Unicode.isUppercaseLetter

/-- parse titlecase letter (general category Lt) -/
def titlecaseLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected titlecase letter (Lt)" do
    tokenFilter Unicode.isTitlecaseLetter

/-- parse other letter (general category Lm) -/
def modifierLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected modifier letter (Lm)" do
    tokenFilter Unicode.isModifierLetter

/-- parse other letter (general category Lo) -/
def otherLetter : ParserT ε σ Char m Char :=
  withErrorMessage "expected other letter (Lo)" do
    tokenFilter Unicode.isOtherLetter

/-- parse mark (general category M) -/
def mark : ParserT ε σ Char m Char :=
  withErrorMessage "expected mark (M)" do
    tokenFilter Unicode.isMark

/-- parse spacing combining mark (general category Mc) -/
def spacingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected spacing mark (Mc)" do
    tokenFilter Unicode.isSpacingMark

/-- parse nonspacing combining mark (general category Mn) -/
def nonspacingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected nonspacing mark (Mn)" do
    tokenFilter Unicode.isNonspacingMark

/-- parse enclosing combining mark (general category Me) -/
def enclosingMark : ParserT ε σ Char m Char :=
  withErrorMessage "expected enclosing mark (Me)" do
    tokenFilter Unicode.isEnclosingMark

/-- parse number (general category N) -/
def number : ParserT ε σ Char m Char :=
  withErrorMessage "expected number (N)" do
    tokenFilter Unicode.isNumber

/-- parse decimal number (general category Nd) -/
def decimalNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected decimal number (Nd)" do
    tokenFilter Unicode.isDecimalNumber

/-- parse letter number (general category Nl) -/
def letterNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter number (Nl)" do
    tokenFilter Unicode.isLetterNumber

/-- parse other number (general category No) -/
def otherNumber : ParserT ε σ Char m Char :=
  withErrorMessage "expected other number (No)" do
    tokenFilter Unicode.isOtherNumber

/-- parse punctuation (general category P) -/
def punctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected punctuation (P)" do
    tokenFilter Unicode.isPunctuation

/-- parse connector punctuation (general category Pc) -/
def connectorPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected connector punctuation (Pc)" do
    tokenFilter Unicode.isConnectorPunctuation

/-- parse dash punctuation (general category Pd) -/
def dashPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected dash punctuation (Pd)" do
    tokenFilter Unicode.isDashPunctuation

/-- parse opening punctuation (general category Ps) -/
def openPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected opening punctuation (Ps)" do
    tokenFilter Unicode.isOpenPunctuation

/-- parse closing punctuation (general category Pe) -/
def closePunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected opening punctuation (Pe)" do
    tokenFilter Unicode.isClosePunctuation

/-- parse initial punctuation (general category Pi) -/
def initialPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected initial punctuation (Pi)" do
    tokenFilter Unicode.isInitialPunctuation

/-- parse final punctuation (general category Pf) -/
def finalPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected final punctuation (Pf)" do
    tokenFilter Unicode.isFinalPunctuation

/-- parse other punctuation (general category Po) -/
def otherPunctuation : ParserT ε σ Char m Char :=
  withErrorMessage "expected other punctuation (Po)" do
    tokenFilter Unicode.isOtherPunctuation

/-- parse symbol (general category S) -/
def symbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected symbol (S)" do
    tokenFilter Unicode.isSymbol

/-- parse math symbol (general category Sm) -/
def mathSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected math symbol (Sm)" do
    tokenFilter Unicode.isMathSymbol

/-- parse currency symbol (general category Sc) -/
def currencySymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected currency symbol (Sc)" do
    tokenFilter Unicode.isCurrencySymbol

/-- parse modifier symbol (general category Sk) -/
def modifierSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected modifier symbol (Sk)" do
    tokenFilter Unicode.isModifierSymbol

/-- parse other symbol (general category So) -/
def otherSymbol : ParserT ε σ Char m Char :=
  withErrorMessage "expected other symbol (So)" do
    tokenFilter Unicode.isOtherSymbol

/-- parse separator (general category Z) -/
def separator : ParserT ε σ Char m Char :=
  withErrorMessage "expected separator (Z)" do
    tokenFilter Unicode.isSeparator

/-- parse space separator (general category Zs) -/
def spaceSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected space separator (Zs)" do
    tokenFilter Unicode.isSpaceSeparator

/-- parse line separator (general category Zl) -/
def lineSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected line separator (Zl)" do
    tokenFilter Unicode.isLineSeparator

/-- parse paragraph separator (general category Zp) -/
def paragraphSeparator : ParserT ε σ Char m Char :=
  withErrorMessage "expected paragraph separator (Zp)" do
    tokenFilter Unicode.isParagraphSeparator

/-- parse other character (general category C) -/
def other : ParserT ε σ Char m Char :=
  withErrorMessage "expected other character (C)" do
    tokenFilter Unicode.isOther

/-- parse control character (general category Cc) -/
def control : ParserT ε σ Char m Char :=
  withErrorMessage "expected control character (Cc)" do
    tokenFilter Unicode.isControl

/-- parse format character (general category Cf) -/
def format : ParserT ε σ Char m Char :=
  withErrorMessage "expected format character (Cf)" do
    tokenFilter Unicode.isFormat

/-- parse surrogate character (general category Cs) -/
def surrogate : ParserT ε σ Char m Char :=
  withErrorMessage "expected surrogate character (Cs)" do
    tokenFilter Unicode.isSurrogate

/-- parse private-use character (general category Co) -/
def privateUse : ParserT ε σ Char m Char :=
  withErrorMessage "expected private-use character (Co)" do
    tokenFilter Unicode.isPrivateUse

/-- parse unassigned character (general category Cn) -/
def noncharacter : ParserT ε σ Char m Char :=
  withErrorMessage "expected unassigned character (Cn)" do
    tokenFilter Unicode.isUnassigned

end Parser.Char.Unicode
