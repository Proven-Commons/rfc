/-
  The calendar rules of RFC 3339, section 5.7, and the checks that
  decide which timestamps are valid.
-/

import Rfc3339.Types

namespace Rfc3339

/-- Leap years of the Gregorian calendar, as in RFC 3339, Appendix C. -/
def isLeapYear (y : Nat) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The number of days in month `m` (1 to 12) of year `y`, and 0 for any
    other `m`. -/
def daysInMonth (y m : Nat) : Nat :=
  match m with
  | 1 => 31 | 2 => if isLeapYear y then 29 else 28 | 3 => 31 | 4 => 30
  | 5 => 31 | 6 => 30 | 7 => 31 | 8 => 31 | 9 => 30 | 10 => 31 | 11 => 30
  | 12 => 31 | _ => 0

/-- The offset in minutes east of UTC. -/
def offsetMinutes : Offset → Int
  | .z => 0
  | .plus h m => (h * 60 + m : Nat)
  | .minus h m => -((h * 60 + m : Nat) : Int)

def Offset.isValid : Offset → Bool
  | .z => true
  | .plus h m => h ≤ 23 && m ≤ 59
  | .minus h m => h ≤ 23 && m ≤ 59

/-- Second 60 is a leap second, which section 5.7 puts at the end of a
    month in UTC. With the offset applied, the time must be 23:59 UTC on
    the last day of a month. Since an offset is less than a day, that is
    either the same day as the local date, at its end, or the day
    before, when the local date is the first of a month. -/
def leapSecondOK (t : Timestamp) : Bool :=
  let u : Int := ((t.hour * 60 + t.minute : Nat) : Int) - offsetMinutes t.offset
  (u == 1439 && t.day == daysInMonth t.year t.month) || (u == -1 && t.day == 1)

/-- Whether `t` is a timestamp RFC 3339 allows: each field in its range
    (section 5.6), the day within its month, and second 60 only for a
    leap second (section 5.7). -/
def Timestamp.isValid (t : Timestamp) : Bool :=
  t.year ≤ 9999 && 1 ≤ t.month && t.month ≤ 12 &&
  1 ≤ t.day && t.day ≤ daysInMonth t.year t.month &&
  t.hour ≤ 23 && t.minute ≤ 59 && t.second ≤ 60 &&
  (t.second != 60 || leapSecondOK t) &&
  t.fraction.all (· < 10) && t.offset.isValid

end Rfc3339
