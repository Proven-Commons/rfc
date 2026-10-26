/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from RFC 3339, are in
  `Spec/Defs.lean`, and the types in `Rfc3339/Types.lean`. Both are part
  of the specification too.
-/

import Rfc3339
import Spec.Defs

open Rfc3339

/-! ## Validity -/

/-- `isValid` decides exactly `Spec.Valid`: the rules of sections 5.6
    and 5.7, except that second 60 is allowed at the end of every month
    in UTC, since no table of the months that had a leap second is
    kept. -/
theorem Spec.isValid_iff (t : Timestamp) : t.isValid = true ↔ Spec.Valid t := sorry

/-! ## Printing -/

/-- A valid timestamp prints as the grammar of section 5.6 writes it,
    with `T` and `Z` in upper case. -/
theorem Spec.print_eq (t : Timestamp) (h : Spec.Valid t) :
    t.print.toList = Spec.render t := sorry

/-! ## Parsing -/

/-- `parse` returns `t` exactly when `t` is valid and the string is how
    `t` is written, with `T` and `Z` in either case. So it accepts
    nothing outside the grammar of section 5.6 and `Spec.Valid`, rejects
    nothing inside them, and returns the fields as written. -/
theorem Spec.parse_iff (s : String) (t : Timestamp) :
    parse s = some t ↔ Spec.Valid t ∧ s.toList.map Spec.asciiUpper = Spec.render t := sorry

/-- What `parse` returns is valid: among other things, the day exists
    in its month, so 30 February never passes. -/
theorem Spec.parse_valid (s : String) (t : Timestamp) (h : parse s = some t) :
    Spec.Valid t := sorry

/-- Round trip: printing a valid timestamp and parsing the result gives
    it back. -/
theorem Spec.parse_print (t : Timestamp) (h : Spec.Valid t) : parse t.print = some t := sorry

/-- Round trip: parsing a string and printing the result gives the
    string back, with `T` and `Z` in upper case. -/
theorem Spec.print_parse (s : String) (t : Timestamp) (h : parse s = some t) :
    t.print.toList = s.toList.map Spec.asciiUpper := sorry

/-! ## Instants -/

/-- `unixSeconds` counts the whole seconds from 1970-01-01T00:00:00Z, by
    the calendar of section 5.7, with the offset applied. -/
theorem Spec.unixSeconds_eq (t : Timestamp) (h : Spec.Valid t) :
    t.unixSeconds = Spec.unixSeconds t := sorry

/-- `compareInstant` orders two timestamps by the instants they name,
    whatever their offsets: by UTC minute, then by the second within it,
    where a leap second comes after 59, then by the fraction. -/
theorem Spec.compareInstant_eq (a b : Timestamp) (ha : Spec.Valid a) (hb : Spec.Valid b) :
    a.compareInstant b = Spec.compareInstants a b := sorry

/-! ## Test vectors -/

/-- The examples of section 5.8, with the fields the RFC reads them
    as. -/
theorem Spec.rfc3339_examples :
    parse "1985-04-12T23:20:50.52Z" = some ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ ∧
    parse "1996-12-19T16:39:57-08:00" = some ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩ ∧
    parse "1990-12-31T23:59:60Z" = some ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ ∧
    parse "1990-12-31T15:59:60-08:00" = some ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ ∧
    parse "1937-01-01T12:00:27.87+00:20" =
      some ⟨1937, 1, 1, 12, 0, 27, [8, 7], .plus 0 20⟩ := sorry

/-- What section 5.8 says about those examples: the second is "equivalent
    to 1996-12-20T00:39:57Z", and the fourth is "the same leap second" as
    the third. And a count worked out apart from the RFC, by Python's
    `calendar.timegm`: the first is 482196050 seconds after the epoch. -/
theorem Spec.rfc3339_example_instants :
    (Timestamp.compareInstant ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩
      ⟨1996, 12, 20, 0, 39, 57, [], .z⟩ = .eq) ∧
    (Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = .eq) ∧
    Timestamp.unixSeconds ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ = 482196050 := sorry

/-- A leap second comes after second 59 of its minute and before the
    next minute, fraction included. Unix seconds, as in POSIX time, give
    it the same count as the second after it. -/
theorem Spec.leap_second_order :
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 59, [9], .z⟩
      ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [5], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [2], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ = .lt ∧
    Timestamp.unixSeconds ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ =
      Timestamp.unixSeconds ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ := sorry

/-- Days outside their month, and the leap year rule of Appendix C. -/
theorem Spec.calendar_vectors :
    (parse "2000-02-29T00:00:00Z").isSome ∧
    (parse "2004-02-29T00:00:00Z").isSome ∧
    parse "1900-02-29T00:00:00Z" = none ∧
    parse "2001-02-29T00:00:00Z" = none ∧
    parse "2000-02-30T00:00:00Z" = none ∧
    parse "2001-04-31T00:00:00Z" = none ∧
    parse "2001-01-32T00:00:00Z" = none ∧
    parse "2001-01-00T00:00:00Z" = none ∧
    parse "2001-00-01T00:00:00Z" = none ∧
    parse "2001-13-01T00:00:00Z" = none := sorry

/-- Second 60 only at the end of a month in UTC. -/
theorem Spec.leap_second_vectors :
    (parse "1990-06-30T23:59:60Z").isSome ∧
    (parse "1991-01-01T00:59:60+01:00").isSome ∧
    parse "1990-12-31T23:59:61Z" = none ∧
    parse "1990-12-31T23:58:60Z" = none ∧
    parse "1990-12-30T23:59:60Z" = none ∧
    parse "1990-12-31T23:59:60+01:00" = none := sorry

/-- Lower case `t` and `z` are read; other spellings are not. -/
theorem Spec.syntax_vectors :
    parse "1985-04-12t23:20:50.52z" = parse "1985-04-12T23:20:50.52Z" ∧
    parse "1985-04-12 23:20:50.52Z" = none ∧
    parse "1985-04-12T23:20:50.Z" = none ∧
    parse "1985-04-12T23:20:50,52Z" = none ∧
    parse "1985-04-12T23:20Z" = none ∧
    parse "85-04-12T23:20:50Z" = none ∧
    parse "1985-04-12T23:20:50+24:00" = none ∧
    parse "1985-04-12T23:20:50+23:60" = none ∧
    parse "1985-04-12T23:20:50+0100" = none ∧
    parse "1985-04-12T23:20:50" = none ∧
    parse "1985-04-12T23:20:50Z " = none ∧
    parse "1985-04-12T24:00:00Z" = none := sorry

/-! ## From Unix seconds -/

/-- `fromUnixSeconds s` gives exactly the timestamp that is valid, in
    UTC (offset `Z`), with no fraction and no leap second, and that
    names the second `s`. There is at most one; the next statement says
    for which `s` there is one. -/
theorem Spec.fromUnixSeconds_iff (s : Int) (t : Timestamp) :
    Rfc3339.fromUnixSeconds s = some t ↔
      Spec.Valid t ∧ t.offset = .z ∧ t.fraction = [] ∧ t.second ≤ 59 ∧
        Spec.unixSeconds t = s := sorry

/-- It gives a timestamp exactly for the seconds from
    0000-01-01T00:00:00Z to 9999-12-31T23:59:59Z, the years RFC 3339
    allows. -/
theorem Spec.fromUnixSeconds_isSome (s : Int) :
    (Rfc3339.fromUnixSeconds s).isSome ↔
      Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ≤ s ∧
        s ≤ Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := sorry

/-- The epoch; the example of section 5.8; a leap day; the last second a
    signed 32-bit count reaches; the second before the epoch; the ends of
    the range, and one second past each. -/
theorem Spec.fromUnixSeconds_vectors :
    Rfc3339.fromUnixSeconds 0 = some ⟨1970, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 482196050 = some ⟨1985, 4, 12, 23, 20, 50, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 951782400 = some ⟨2000, 2, 29, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 2147483647 = some ⟨2038, 1, 19, 3, 14, 7, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-1) = some ⟨1969, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ = -62167219200 ∧
    Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 253402300799 ∧
    Rfc3339.fromUnixSeconds (-62167219200) = some ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 253402300799 = some ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-62167219201) = none ∧
    Rfc3339.fromUnixSeconds 253402300800 = none := sorry
