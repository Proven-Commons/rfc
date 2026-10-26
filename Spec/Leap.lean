/-
  The definitions the leap second statements use: the table of leap
  seconds and TAI − UTC as tzdata's `leap-seconds.list` publishes it,
  from IERS Bulletin C, and section 5.7 of RFC 3339 with that table.
  Part of the approved specification, with `Spec.lean` and
  `Spec/Defs.lean`, and written independently of the code in
  `Rfc3339/`.
-/

import Spec.Defs

open Rfc3339

/-! ## The table

`leap-seconds.list`, as tzdata 2026e ships it in
`/usr/share/zoneinfo/leap-seconds.list`, is "Updated through IERS
Bulletin C", its last update at NTP time 3992312697 (its `#$` line), and
its own hash line reads `#h a9bad145 84c31c70 758402aa b37bfd54
5923836a`. It defines its columns so: "NTP timestamp (X parameter) is
the number of seconds since 1900.0", and "DTAI: The difference DTAI=
TAI-UTC in units of seconds. It is the quantity to add to UTC to get the
time in TAI". NTP time counts 86400 seconds to every day. Each data line
is an NTP time and the DTAI from then on:

```
2272060800      10      # 1 Jan 1972
2287785600      11      # 1 Jul 1972
2303683200      12      # 1 Jan 1973
2335219200      13      # 1 Jan 1974
2366755200      14      # 1 Jan 1975
2398291200      15      # 1 Jan 1976
2429913600      16      # 1 Jan 1977
2461449600      17      # 1 Jan 1978
2492985600      18      # 1 Jan 1979
2524521600      19      # 1 Jan 1980
2571782400      20      # 1 Jul 1981
2603318400      21      # 1 Jul 1982
2634854400      22      # 1 Jul 1983
2698012800      23      # 1 Jul 1985
2776982400      24      # 1 Jan 1988
2840140800      25      # 1 Jan 1990
2871676800      26      # 1 Jan 1991
2918937600      27      # 1 Jul 1992
2950473600      28      # 1 Jul 1993
2982009600      29      # 1 Jul 1994
3029443200      30      # 1 Jan 1996
3076704000      31      # 1 Jul 1997
3124137600      32      # 1 Jan 1999
3345062400      33      # 1 Jan 2006
3439756800      34      # 1 Jan 2009
3550089600      35      # 1 Jul 2012
3644697600      36      # 1 Jul 2015
3692217600      37      # 1 Jan 2017
```

"File expires on 28 June 2027": the table holds until then. The first
line is the start of UTC as it is now, with TAI − UTC 10; each later
line follows a leap second, the second 23:59:60 UTC just before it. The
file adds that "so far, all leap seconds have been positive (a second has
been added to UTC)".
-/

/-- The table, line for line: NTP time, and TAI − UTC from then on. -/
def Spec.leapTable : List (Nat × Nat) :=
  [(2272060800, 10), (2287785600, 11), (2303683200, 12), (2335219200, 13),
   (2366755200, 14), (2398291200, 15), (2429913600, 16), (2461449600, 17),
   (2492985600, 18), (2524521600, 19), (2571782400, 20), (2603318400, 21),
   (2634854400, 22), (2698012800, 23), (2776982400, 24), (2840140800, 25),
   (2871676800, 26), (2918937600, 27), (2950473600, 28), (2982009600, 29),
   (3029443200, 30), (3076704000, 31), (3124137600, 32), (3345062400, 33),
   (3439756800, 34), (3550089600, 35), (3644697600, 36), (3692217600, 37)]

/-- NTP time from Unix seconds: NTP counts from 1900-01-01T00:00:00Z,
    70 years of 86400-second days, 17 of them leap years, before the
    Unix epoch. -/
def Spec.ntpOfUnix (u : Int) : Int := u + (70 * 365 + 17) * 86400

example : Spec.ntpOfUnix 0 = 2208988800 := by decide

/-! ## Section 5.7, with the table

"the leap second point is shifted by the zone offset (so it happens at
the same instant around the globe)": a timestamp with second 60 is a
leap second of the table when its Unix seconds, which count second 60
as the start of the next minute, are those of a line after the first.
-/

/-- `t` names one of the table's leap seconds: its second is 60, and the
    time just after it, in NTP time, is that of a line of the table
    after the first. -/
def Spec.TableLeapSecond (t : Timestamp) : Prop :=
  t.second = 60 ∧ ∃ e ∈ Spec.leapTable.tail, Spec.ntpOfUnix (Spec.unixSeconds t) = e.1

/-- Valid, by section 5.7 with the table: as `Spec.Valid`, and second 60
    only at a leap second of the table. -/
def Spec.ValidKnown (t : Timestamp) : Prop :=
  Spec.Valid t ∧ (t.second = 60 → Spec.TableLeapSecond t)

/-! ## SI seconds and TAI − UTC -/

/-- The place of a timestamp's whole second in UTC order: its UTC minute
    and its second, with 61 places to a minute, as `Spec.instantKey`
    with no fraction. -/
def Spec.secondKey (t : Timestamp) : Int := Spec.utcMinute t * 61 + t.second

/-- The same place for the leap second just before NTP time `ntp`:
    second 60 of the minute before it. -/
def Spec.leapSecondKey (ntp : Nat) : Int :=
  (((ntp : Int) - Spec.ntpOfUnix 0) / 60 + ((Spec.dayNumber 1970 1 1 * 1440 : Nat) : Int) - 1) * 61 + 60

/-- How many leap seconds of the table come before the second `t` falls
    in. -/
def Spec.leapsBefore (t : Timestamp) : Nat :=
  (Spec.leapTable.tail.filter fun e => Spec.leapSecondKey e.1 < Spec.secondKey t).length

/-- SI seconds from 1972-01-01T00:00:00Z to `t`, without its fraction:
    the Unix seconds between them, which count 86400 to every day, and
    one more for each leap second of the table between them. -/
def Spec.siSeconds (t : Timestamp) : Int :=
  Spec.unixSeconds t - Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ + Spec.leapsBefore t

/-- TAI − UTC at NTP time `ntp`: the value on the table's last line at
    or before it. -/
def Spec.taiMinusUtcAt (ntp : Int) : Nat :=
  ((Spec.leapTable.filter fun e => (e.1 : Int) ≤ ntp).getLast?.map (·.2)).getD 0

example : Spec.taiMinusUtcAt 2272060800 = 10 ∧ Spec.taiMinusUtcAt 3692217599 = 36 ∧
    Spec.taiMinusUtcAt 3692217600 = 37 := by decide
