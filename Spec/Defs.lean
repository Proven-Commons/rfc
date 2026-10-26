/-
  The definitions the specification uses, written from RFC 3339
  independently of the code in `Rfc3339/`. Part of the approved
  specification, with `Spec.lean` and `Rfc3339/Types.lean`.

  Both the challenge file and the proofs import this file, so each
  statement means the same thing on both sides. The `example`s check
  the definitions against the RFC's tables and against dates whose day
  counts are known. A mistake in either fails the build.
-/

import Rfc3339

open Rfc3339

/-! ## Characters -/

/-- ASCII upper case: `a` to `z` (code points 97 to 122) become `A` to
    `Z`; nothing else changes. -/
def Spec.asciiUpper (c : Char) : Char :=
  if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then Char.ofNat (c.toNat - 32) else c

example : "azAZ09-:.+tz".toList.map Spec.asciiUpper = "AZAZ09-:.+TZ".toList := by decide

/-- The decimal digit for `n`, for `n` from 0 to 9. -/
def Spec.digitChar (n : Nat) : Char := "0123456789".toList.getD n '?'

/-- The last `k` decimal digits of `n`, most significant first, with
    leading zeros. -/
def Spec.digits (k n : Nat) : List Char :=
  (List.range k).reverse.map fun i => Spec.digitChar (n / 10 ^ i % 10)

example : Spec.digits 4 1985 = "1985".toList := by decide
example : Spec.digits 4 7 = "0007".toList := by decide
example : Spec.digits 2 9 = "09".toList := by decide

/-! ## The format: RFC 3339, section 5.6

```
date-fullyear   = 4DIGIT
date-month      = 2DIGIT  ; 01-12
date-mday       = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on
                          ; month/year
time-hour       = 2DIGIT  ; 00-23
time-minute     = 2DIGIT  ; 00-59
time-second     = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second
                          ; rules
time-secfrac    = "." 1*DIGIT
time-numoffset  = ("+" / "-") time-hour ":" time-minute
time-offset     = "Z" / time-numoffset

partial-time    = time-hour ":" time-minute ":" time-second
                  [time-secfrac]
full-date       = date-fullyear "-" date-month "-" date-mday
full-time       = partial-time time-offset

date-time       = full-date "T" full-time
```

The note under the grammar lets `T` and `Z` be written in lower case
too. `render` writes them in upper case; `Spec.parse_iff` in
`Spec.lean` says how the parser treats the lower case forms. -/

/-- `time-offset`. -/
def Spec.renderOffset : Offset → List Char
  | .z => ['Z']
  | .plus h m => ['+'] ++ Spec.digits 2 h ++ [':'] ++ Spec.digits 2 m
  | .minus h m => ['-'] ++ Spec.digits 2 h ++ [':'] ++ Spec.digits 2 m

/-- `date-time`, with `T` and `Z` in upper case. The fraction is written
    when there is at least one digit. -/
def Spec.render (t : Timestamp) : List Char :=
  Spec.digits 4 t.year ++ ['-'] ++ Spec.digits 2 t.month ++ ['-'] ++ Spec.digits 2 t.day ++
    ['T'] ++ Spec.digits 2 t.hour ++ [':'] ++ Spec.digits 2 t.minute ++ [':'] ++
    Spec.digits 2 t.second ++
    (if t.fraction = [] then [] else ['.'] ++ t.fraction.map Spec.digitChar) ++
    Spec.renderOffset t.offset

example : Spec.render ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ =
    "1985-04-12T23:20:50.52Z".toList := by decide
example : Spec.render ⟨1937, 1, 1, 12, 0, 27, [8, 7], .plus 0 20⟩ =
    "1937-01-01T12:00:27.87+00:20".toList := by decide
example : Spec.render ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩ =
    "1996-12-19T16:39:57-08:00".toList := by decide

/-! ## The calendar: RFC 3339, section 5.7 and Appendix C -/

/-- Appendix C: a year divisible by 4 is a leap year, except one
    divisible by 100, except one divisible by 400. -/
def Spec.isLeapYear (y : Nat) : Bool :=
  decide (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))

example : [1900, 1996, 1997, 2000, 2100, 2400, 0].map Spec.isLeapYear =
    [false, true, false, true, false, true, true] := by decide

/-- Section 5.7, the maximum value of `date-mday` for month `m` of year
    `y`; 0 when `m` is not a month. -/
def Spec.daysInMonth (y m : Nat) : Nat :=
  if m = 2 then (if Spec.isLeapYear y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else if 1 ≤ m ∧ m ≤ 12 then 31
  else 0

-- The table of section 5.7, month by month, for a common year and a
-- leap year.
example : (List.range 14).map (Spec.daysInMonth 2001) =
    [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 0] := by decide
example : (List.range 14).map (Spec.daysInMonth 2004) =
    [0, 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 0] := by decide

def Spec.yearLength (y : Nat) : Nat := if Spec.isLeapYear y then 366 else 365

/-- The number of days from 0000-01-01 to the date `y`-`m`-`d`, in the
    Gregorian calendar extended back to year 0, which RFC 3339 uses
    (section 5.7 and Appendix C): the lengths of the years before `y`,
    then of the months before `m` in year `y`, then the days before
    `d`. -/
def Spec.dayNumber (y m d : Nat) : Nat :=
  ((List.range y).map Spec.yearLength).sum +
    ((List.range (m - 1)).map fun i => Spec.daysInMonth y (i + 1)).sum + (d - 1)

-- Known counts: 1970-01-01 is day 719528 (Python's
-- `date(1970, 1, 1).toordinal()`, 719163, counts from 0001-01-01 as day
-- 1, and year 0 is a leap year of 366 days), and 2000-03-01 is 11017
-- days later.
example : Spec.dayNumber 0 1 1 = 0 := by decide
example : Spec.dayNumber 1 1 1 = 366 := by decide
example : Spec.dayNumber 1970 1 1 = 719528 := by decide +kernel
example : Spec.dayNumber 2000 3 1 = 719528 + 11017 := by decide +kernel

/-! ## Validity -/

/-- `time-numoffset`: hours 00 to 23 and minutes 00 to 59. -/
def Spec.OffsetValid : Offset → Prop
  | .z => True
  | .plus h m => h ≤ 23 ∧ m ≤ 59
  | .minus h m => h ≤ 23 ∧ m ≤ 59

/-- The offset in minutes: local time minus UTC. -/
def Spec.offsetMinutes : Offset → Int
  | .z => 0
  | .plus h m => (h : Int) * 60 + m
  | .minus h m => -((h : Int) * 60 + m)

/-- The minute the timestamp falls in, counted in UTC from
    0000-01-01T00:00Z. Local time is UTC plus the offset, so the offset
    is subtracted. -/
def Spec.utcMinute (t : Timestamp) : Int :=
  ((Spec.dayNumber t.year t.month t.day * 1440 + t.hour * 60 + t.minute : Nat) : Int) -
    Spec.offsetMinutes t.offset

/-- Section 5.7: `time-second` may be 60 "at the end of months in which
    a leap second occurs", and in other time zones "the leap second point
    is shifted by the zone offset (so it happens at the same instant
    around the globe)". So the minute the leap second falls in, in UTC,
    is the last one before a month begins. No table of the months that
    had a leap second is kept, so every month is allowed. -/
def Spec.LeapSecondAllowed (t : Timestamp) : Prop :=
  ∃ y m, 1 ≤ m ∧ m ≤ 12 ∧ Spec.utcMinute t + 1 = ((Spec.dayNumber y m 1 * 1440 : Nat) : Int)

/-- A timestamp RFC 3339 allows: every field in the range section 5.6
    gives it, the day within its month (section 5.7), and second 60 only
    for a leap second. -/
def Spec.Valid (t : Timestamp) : Prop :=
  t.year ≤ 9999 ∧
  1 ≤ t.month ∧ t.month ≤ 12 ∧
  1 ≤ t.day ∧ t.day ≤ Spec.daysInMonth t.year t.month ∧
  t.hour ≤ 23 ∧ t.minute ≤ 59 ∧ t.second ≤ 60 ∧
  (t.second = 60 → Spec.LeapSecondAllowed t) ∧
  (∀ d ∈ t.fraction, d ≤ 9) ∧
  Spec.OffsetValid t.offset

/-! ## Instants -/

/-- Whole seconds from 1970-01-01T00:00:00Z to the timestamp. Second 60
    counts as 60 seconds into its minute, so a leap second gives the
    same number as the second after it, as POSIX time does. -/
def Spec.unixSeconds (t : Timestamp) : Int :=
  (Spec.utcMinute t - ((Spec.dayNumber 1970 1 1 * 1440 : Nat) : Int)) * 60 + t.second

/-- The fraction's digits read as a whole number: `[5, 2]` is 52. -/
def Spec.fractionValue (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => 10 * acc + d) 0

example : Spec.fractionValue [0, 5, 2] = 52 := by decide

/-- The place of the timestamp's instant in UTC order, in units of
    `10 ^ (-k)` seconds, for `k` at least the number of fraction digits.
    Each UTC minute has 61 places for seconds 0 to 60, so a leap second
    comes after second 59 of its minute and before the next minute.
    Only the order of these numbers is used, not their size. -/
def Spec.instantKey (t : Timestamp) (k : Nat) : Int :=
  (Spec.utcMinute t * 61 + t.second) * 10 ^ k +
    Spec.fractionValue t.fraction * 10 ^ (k - t.fraction.length)

/-- The order of the instants two timestamps name: by UTC minute, then
    by the second within it, then by the fraction, compared exactly. -/
def Spec.compareInstants (a b : Timestamp) : Ordering :=
  let k := max a.fraction.length b.fraction.length
  compare (Spec.instantKey a k) (Spec.instantKey b k)
