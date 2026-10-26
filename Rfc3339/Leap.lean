/-
  Leap seconds: the table of the months that ended in one, validity by
  that table as section 5.7 asks, SI seconds since 1972 that give each
  leap second a number of its own, and TAI − UTC.
-/

import Rfc3339.FromUnix

namespace Rfc3339

/-- The months, as (year, month), whose last second in UTC was a leap
    second, 23:59:60: the 27 of IERS Bulletin C, as tzdata's
    `leap-seconds.list` gives them. That file expires on 28 June 2027:
    no leap second comes before then that is not in it. The lemma
    `Rfc3339.Proofs.Leap.leapKey_table`, in `Proofs/Leap/Table.lean`,
    proves that these months give the leap seconds of the lines of
    `Spec.leapTable` after the first, in the same order. The README's
    "Refresh the leap second table" says how to update the list. -/
def leapMonths : List (Nat × Nat) :=
  [(1972, 6), (1972, 12), (1973, 12), (1974, 12), (1975, 12), (1976, 12), (1977, 12),
   (1978, 12), (1979, 12), (1981, 6), (1982, 6), (1983, 6), (1985, 6), (1987, 12),
   (1989, 12), (1990, 12), (1992, 6), (1993, 6), (1994, 6), (1995, 12), (1997, 6),
   (1998, 12), (2005, 12), (2008, 12), (2012, 6), (2015, 6), (2016, 12)]

/-- The year and month, in UTC, of the minute the timestamp falls in.
    There is one edge case. A timestamp on 0000-01-01 with a positive
    offset can name an instant before 0000-01-01T00:00:00Z, as
    `0000-01-01T00:59:60+01:00` does. Its UTC month is the December
    before year 0000, which a `Nat` year cannot hold, and the result is
    (0, 1). This cannot change `isValidKnown`. (0, 1) is not in
    `leapMonths`, which starts in 1972. And `Spec.isValidKnown_iff`
    proves, for every timestamp, that `isValidKnown` agrees with
    `Spec.ValidKnown`, which reads Unix seconds through the table, not
    `utcMonth`. So if (0, 1) ever joined `leapMonths`, that proof would
    fail. -/
def Timestamp.utcMonth (t : Timestamp) : Nat × Nat :=
  let (y, m, _) := fromDayNumber (t.utcMinute / 1440).toNat
  (y, m)

/-- Whether `t` is valid and, if its second is 60, one of the leap
    seconds of the table: section 5.7 allows second 60 only "at the end
    of months in which a leap second occurs". -/
def Timestamp.isValidKnown (t : Timestamp) : Bool :=
  t.isValid && (t.second != 60 || leapMonths.contains t.utcMonth)

/-- The place of the leap second at the end of month `ym` in the order
    `utcMinute * 61 + second`: second 60 of the last minute before the
    next month. -/
def leapKey (ym : Nat × Nat) : Int :=
  let next := if ym.2 = 12 then dayNumber (ym.1 + 1) 1 1 else dayNumber ym.1 (ym.2 + 1) 1
  (((next * 1440 : Nat) : Int) - 1) * 61 + 60

/-- How many leap seconds of the table come before the second the
    timestamp falls in. -/
def Timestamp.leapsBefore (t : Timestamp) : Nat :=
  (leapMonths.filter fun ym => leapKey ym < t.utcMinute * 61 + t.second).length

/-- SI seconds from 1972-01-01T00:00:00Z to the timestamp, leaving out
    the fraction: Unix seconds, which give each day 86400, and one more
    for each leap second of the table before it. 63072000 is the Unix
    seconds of 1972-01-01T00:00:00Z. Before that instant the result is
    only a formal value: Unix seconds less 63072000, 86400 to a day.
    UTC then ran on seconds of varying length, so these are not SI
    seconds. SPEC.md says so under "Leap seconds, with the table", as
    does `Spec.siSeconds_eq`. -/
def Timestamp.siSeconds (t : Timestamp) : Int :=
  t.unixSeconds - 63072000 + t.leapsBefore

/-- TAI − UTC at the timestamp, in seconds: 10 from the start of 1972,
    and one more after each leap second. Before 1972-01-01T00:00:00Z
    the result is only a formal value, 10, with no meaning. TAI − UTC
    was then not a whole number of seconds. The tool's `known` request
    prints `-` for it there. SPEC.md says so under "Leap seconds, with
    the table", as does `Spec.taiMinusUtc_leapsBefore`. -/
def Timestamp.taiMinusUtc (t : Timestamp) : Nat :=
  10 + t.leapsBefore

/-- The SI seconds of each leap second of the table. -/
def leapSiSeconds : List Int :=
  (leapMonths.zipIdx).map fun (ym, i) => (leapKey ym + 1) / 61 * 60 - 719528 * 86400 - 63072000 + i

/-- The UTC timestamp `n` SI seconds after 1972-01-01T00:00:00Z, with
    second 60 at each leap second of the table, no fraction, and offset
    `Z`; `none` below 0 or after 9999-12-31T23:59:59Z. -/
def fromSiSeconds (n : Int) : Option Timestamp :=
  if n < 0 then none
  else
    let k := (leapSiSeconds.filter (· < n)).length
    if leapSiSeconds.contains n then
      (fromUnixSeconds (n + 63072000 - k - 1)).map fun t => { t with second := 60 }
    else fromUnixSeconds (n + 63072000 - k)

end Rfc3339
