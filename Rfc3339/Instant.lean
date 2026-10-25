/-
  The instant a timestamp names: whole seconds since the Unix epoch,
  and an order on instants that counts the fraction.
-/

import Rfc3339.Calendar

namespace Rfc3339

/-- Days from 0000-01-01 to the first day of year `y`, in the proleptic
    Gregorian calendar: 365 a year, and one more for each year below `y`
    that is a multiple of 4, less those that are multiples of 100, plus
    those that are multiples of 400. -/
def daysBeforeYear (y : Nat) : Nat :=
  365 * y + (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400

/-- Days from the first of the year to the first of month `m`, for `m`
    from 1 to 12. -/
def daysBeforeMonth (y m : Nat) : Nat :=
  let base := match m with
    | 1 => 0 | 2 => 31 | 3 => 59 | 4 => 90 | 5 => 120 | 6 => 151
    | 7 => 181 | 8 => 212 | 9 => 243 | 10 => 273 | 11 => 304 | _ => 334
  if 2 < m && isLeapYear y then base + 1 else base

/-- Days from 0000-01-01 to the date. -/
def dayNumber (y m d : Nat) : Nat :=
  daysBeforeYear y + daysBeforeMonth y m + (d - 1)

/-- Seconds from 1970-01-01T00:00:00Z to the timestamp, leaving out the
    fraction. 719528 is `dayNumber 1970 1 1`. A leap second counts as
    the first second of the next minute, as in POSIX time, so
    `23:59:60Z` gives the same number as the midnight after it. -/
def Timestamp.unixSeconds (t : Timestamp) : Int :=
  ((dayNumber t.year t.month t.day : Nat) - 719528 : Int) * 86400 +
    ((t.hour * 3600 + t.minute * 60 + t.second : Nat) : Int) - offsetMinutes t.offset * 60

/-- Compares two digit strings as fractions: a missing digit counts as
    0. -/
def compareFraction : List Nat → List Nat → Ordering
  | [], [] => .eq
  | a :: as, [] => if a = 0 then compareFraction as [] else .gt
  | [], b :: bs => if b = 0 then compareFraction [] bs else .lt
  | a :: as, b :: bs =>
    if a < b then .lt else if b < a then .gt else compareFraction as bs

/-- Orders two timestamps by the instant they name, fraction included,
    whatever their offsets. -/
def Timestamp.compareInstant (a b : Timestamp) : Ordering :=
  match compare a.unixSeconds b.unixSeconds with
  | .eq => compareFraction a.fraction b.fraction
  | o => o

end Rfc3339
