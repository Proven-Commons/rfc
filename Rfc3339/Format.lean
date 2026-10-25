/-
  Reading and writing the `date-time` format of RFC 3339, section 5.6.
-/

import Rfc3339.Calendar

namespace Rfc3339

/-! ## Printing -/

/-- The ASCII digit for `n`, for `n` from 0 to 9. -/
def digitChar (n : Nat) : Char := Char.ofNat (n + 48)

/-- `n` in two digits, for `n` below 100. -/
def pad2 (n : Nat) : List Char :=
  [digitChar (n / 10 % 10), digitChar (n % 10)]

/-- `n` in four digits, for `n` below 10000. -/
def pad4 (n : Nat) : List Char :=
  [digitChar (n / 1000 % 10), digitChar (n / 100 % 10), digitChar (n / 10 % 10),
   digitChar (n % 10)]

def Offset.render : Offset → List Char
  | .z => ['Z']
  | .plus h m => '+' :: pad2 h ++ ':' :: pad2 m
  | .minus h m => '-' :: pad2 h ++ ':' :: pad2 m

def renderFraction : List Nat → List Char
  | [] => []
  | ds => '.' :: ds.map digitChar

def Timestamp.render (t : Timestamp) : List Char :=
  pad4 t.year ++ '-' :: pad2 t.month ++ '-' :: pad2 t.day ++ 'T' ::
    pad2 t.hour ++ ':' :: pad2 t.minute ++ ':' :: pad2 t.second ++
    renderFraction t.fraction ++ t.offset.render

/-- The timestamp in RFC 3339 form, with `T` and `Z` in upper case and
    the fraction digit for digit. -/
def Timestamp.print (t : Timestamp) : String :=
  String.ofList t.render

/-! ## Parsing -/

/-- The value of an ASCII digit. -/
def digitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48) else none

/-- ASCII upper case: `a` to `z` become `A` to `Z`, nothing else
    changes. -/
def asciiUpper (c : Char) : Char :=
  if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

def two (a b : Char) : Option Nat := do
  let x ← digitValue a
  let y ← digitValue b
  pure (10 * x + y)

def four (a b c d : Char) : Option Nat := do
  let w ← digitValue a
  let x ← digitValue b
  let y ← digitValue c
  let z ← digitValue d
  pure (1000 * w + 100 * x + 10 * y + z)

/-- The digits at the front of the list, and what follows them. -/
def takeDigits : List Char → List Nat × List Char
  | [] => ([], [])
  | c :: cs =>
    match digitValue c with
    | some v => let r := takeDigits cs; (v :: r.1, r.2)
    | none => ([], c :: cs)

/-- `time-secfrac`, if present: a point and one or more digits. -/
def parseFraction : List Char → Option (List Nat × List Char)
  | '.' :: cs =>
    let r := takeDigits cs
    if r.1.isEmpty then none else some r
  | cs => some ([], cs)

/-- `time-offset`, which must end the input. -/
def parseOffset : List Char → Option Offset
  | ['Z'] => some .z
  | ['+', h1, h2, ':', m1, m2] => do
    let h ← two h1 h2
    let m ← two m1 m2
    pure (.plus h m)
  | ['-', h1, h2, ':', m1, m2] => do
    let h ← two h1 h2
    let m ← two m1 m2
    pure (.minus h m)
  | _ => none

/-- `date-time`, with `T` and `Z` in upper case. -/
def parseUpper : List Char → Option Timestamp
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: 'T' ::
      h1 :: h2 :: ':' :: n1 :: n2 :: ':' :: s1 :: s2 :: rest => do
    let year ← four y1 y2 y3 y4
    let month ← two m1 m2
    let day ← two d1 d2
    let hour ← two h1 h2
    let minute ← two n1 n2
    let second ← two s1 s2
    let r ← parseFraction rest
    let offset ← parseOffset r.2
    let t : Timestamp := { year, month, day, hour, minute, second, fraction := r.1, offset }
    if t.isValid then some t else none
  | _ => none

/-- Reads an RFC 3339 `date-time`. `T` and `Z` may be in either case, as
    the note in section 5.6 allows; nothing else is accepted, and the
    whole string must be the timestamp. -/
def parse (s : String) : Option Timestamp :=
  parseUpper (s.toList.map asciiUpper)

end Rfc3339
