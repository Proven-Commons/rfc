/-
  From Unix seconds back to a timestamp: the UTC timestamp, with no
  fraction and no leap second, that names a given second.
-/

import Rfc3339.Instant

namespace Rfc3339

/-- The year that day `n` falls in, counting 0000-01-01 as day 0. A year
    averages 146097 / 400 days, so `n * 400 / 146097` is off by at most
    one; the year's first day settles it. -/
def yearOfDay (n : Nat) : Nat :=
  let y := n * 400 / 146097
  if daysBeforeYear (y + 1) ≤ n then y + 1
  else if n < daysBeforeYear y then y - 1
  else y

/-- The month that day `doy` of year `y` falls in, counting the first of
    January as day 0: how many months start on or before it. -/
def monthOfDay (y doy : Nat) : Nat :=
  ((List.range 12).filter fun i => daysBeforeMonth y (i + 1) ≤ doy).length

/-- Year, month and day of day `n`, counting 0000-01-01 as day 0. -/
def fromDayNumber (n : Nat) : Nat × Nat × Nat :=
  let y := yearOfDay n
  let doy := n - daysBeforeYear y
  let m := monthOfDay y doy
  (y, m, doy - daysBeforeMonth y m + 1)

/-- The UTC timestamp for `s` seconds since 1970-01-01T00:00:00Z, with
    offset `Z`, no fraction and a second of at most 59; `none` before
    0000-01-01T00:00:00Z or after 9999-12-31T23:59:59Z. 719528 is
    `dayNumber 1970 1 1`. -/
def fromUnixSeconds (s : Int) : Option Timestamp :=
  let t := s + 719528 * 86400
  if 0 ≤ t ∧ t < (daysBeforeYear 10000 : Int) * 86400 then
    let n := t.toNat / 86400
    let secs := t.toNat % 86400
    let (y, m, d) := fromDayNumber n
    some { year := y, month := m, day := d, hour := secs / 3600, minute := secs % 3600 / 60,
           second := secs % 60, fraction := [], offset := .z }
  else none

end Rfc3339
