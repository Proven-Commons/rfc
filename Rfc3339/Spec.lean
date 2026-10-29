/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Rfc3339/Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from RFC 3339, are in
  `Spec/Defs.lean`, and the types in `Rfc3339/Types.lean`. Both are part
  of the specification too.
-/

import Rfc3339
import Rfc3339.Spec.Defs
import Rfc3339.Spec.Leap
import Rfc3339.Spec.Ixdtf

open Rfc3339

/-! ## Validity -/

/-- `isValid` decides exactly `Rfc3339.Spec.Valid`: the rules of sections 5.6
    and 5.7, except that second 60 is allowed at the end of every month
    in UTC, since no table of the months that had a leap second is
    kept. -/
theorem Rfc3339.Spec.isValid_iff (t : Timestamp) : t.isValid = true ↔ Rfc3339.Spec.Valid t := sorry

/-! ## Printing -/

/-- A valid timestamp prints as the grammar of section 5.6 writes it,
    with `T` and `Z` in upper case. -/
theorem Rfc3339.Spec.print_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.print.toList = Rfc3339.Spec.render t := sorry

/-! ## Parsing -/

/-- `parse` returns `t` exactly when `t` is valid and the string is how
    `t` is written, with `T` and `Z` in either case. So it accepts
    nothing outside the grammar of section 5.6 and `Rfc3339.Spec.Valid`, rejects
    nothing inside them, and returns the fields as written. -/
theorem Rfc3339.Spec.parse_iff (s : String) (t : Timestamp) :
    parse s = some t ↔ Rfc3339.Spec.Valid t ∧ s.toList.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render t := sorry

/-- What `parse` returns is valid: among other things, the day exists
    in its month, so 30 February never passes. -/
theorem Rfc3339.Spec.parse_valid (s : String) (t : Timestamp) (h : parse s = some t) :
    Rfc3339.Spec.Valid t := sorry

/-- Round trip: printing a valid timestamp and parsing the result gives
    it back. -/
theorem Rfc3339.Spec.parse_print (t : Timestamp) (h : Rfc3339.Spec.Valid t) : parse t.print = some t := sorry

/-- Round trip: parsing a string and printing the result gives the
    string back, with `T` and `Z` in upper case. -/
theorem Rfc3339.Spec.print_parse (s : String) (t : Timestamp) (h : parse s = some t) :
    t.print.toList = s.toList.map Rfc3339.Spec.asciiUpper := sorry

/-! ## Instants -/

/-- `unixSeconds` counts the whole seconds from 1970-01-01T00:00:00Z, by
    the calendar of section 5.7, with the offset applied. -/
theorem Rfc3339.Spec.unixSeconds_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.unixSeconds = Rfc3339.Spec.unixSeconds t := sorry

/-- `compareInstant` orders two timestamps by the instants they name,
    whatever their offsets: by UTC minute, then by the second within it,
    where a leap second comes after 59, then by the fraction. -/
theorem Rfc3339.Spec.compareInstant_eq (a b : Timestamp) (ha : Rfc3339.Spec.Valid a) (hb : Rfc3339.Spec.Valid b) :
    a.compareInstant b = Rfc3339.Spec.compareInstants a b := sorry

/-! ## Test vectors -/

/-- The examples of section 5.8, with the fields the RFC reads them
    as. -/
theorem Rfc3339.Spec.rfc3339_examples :
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
theorem Rfc3339.Spec.rfc3339_example_instants :
    (Timestamp.compareInstant ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩
      ⟨1996, 12, 20, 0, 39, 57, [], .z⟩ = .eq) ∧
    (Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = .eq) ∧
    Timestamp.unixSeconds ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ = 482196050 := sorry

/-- A leap second comes after second 59 of its minute and before the
    next minute, fraction included. Unix seconds, as in POSIX time, give
    it the same count as the second after it. -/
theorem Rfc3339.Spec.leap_second_order :
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 59, [9], .z⟩
      ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [5], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [2], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ = .lt ∧
    Timestamp.unixSeconds ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ =
      Timestamp.unixSeconds ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ := sorry

/-- Days outside their month, and the leap year rule of Appendix C. -/
theorem Rfc3339.Spec.calendar_vectors :
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
theorem Rfc3339.Spec.leap_second_vectors :
    (parse "1990-06-30T23:59:60Z").isSome ∧
    (parse "1991-01-01T00:59:60+01:00").isSome ∧
    parse "1990-12-31T23:59:61Z" = none ∧
    parse "1990-12-31T23:58:60Z" = none ∧
    parse "1990-12-30T23:59:60Z" = none ∧
    parse "1990-12-31T23:59:60+01:00" = none := sorry

/-- Lower case `t` and `z` are read; other spellings are not. -/
theorem Rfc3339.Spec.syntax_vectors :
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
theorem Rfc3339.Spec.fromUnixSeconds_iff (s : Int) (t : Timestamp) :
    Rfc3339.fromUnixSeconds s = some t ↔
      Rfc3339.Spec.Valid t ∧ t.offset = .z ∧ t.fraction = [] ∧ t.second ≤ 59 ∧
        Rfc3339.Spec.unixSeconds t = s := sorry

/-- It gives a timestamp exactly for the seconds from
    0000-01-01T00:00:00Z to 9999-12-31T23:59:59Z, the years RFC 3339
    allows. -/
theorem Rfc3339.Spec.fromUnixSeconds_isSome (s : Int) :
    (Rfc3339.fromUnixSeconds s).isSome ↔
      Rfc3339.Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ≤ s ∧
        s ≤ Rfc3339.Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := sorry

/-- 0096-12-31 at midnight, from the year-start grid; the epoch; the
    example of section 5.8; a leap day; the last second a
    signed 32-bit count reaches; the second before the epoch; the ends of
    the range, and one second past each. -/
theorem Rfc3339.Spec.fromUnixSeconds_vectors :
    Rfc3339.fromUnixSeconds (-59106153600) = some ⟨96, 12, 31, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 0 = some ⟨1970, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 482196050 = some ⟨1985, 4, 12, 23, 20, 50, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 951782400 = some ⟨2000, 2, 29, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 2147483647 = some ⟨2038, 1, 19, 3, 14, 7, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-1) = some ⟨1969, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Rfc3339.Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ = -62167219200 ∧
    Rfc3339.Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 253402300799 ∧
    Rfc3339.fromUnixSeconds (-62167219200) = some ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 253402300799 = some ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-62167219201) = none ∧
    Rfc3339.fromUnixSeconds 253402300800 = none := sorry

/-! ## Leap seconds, with the table -/

/-- `isValidKnown` decides section 5.7 with the table of leap seconds:
    as `isValid`, but second 60 only at one of the table's leap seconds,
    at the same instant whatever the offset. -/
theorem Rfc3339.Spec.isValidKnown_iff (t : Timestamp) :
    t.isValidKnown = true ↔ Rfc3339.Spec.ValidKnown t := sorry

/-- `siSeconds` is the Unix seconds from 1972-01-01T00:00:00Z to the
    timestamp, leaving out the fraction, and one more for each leap
    second of the table before it. From 1972 on, those are the SI
    seconds between them; before 1972 there are no leap seconds, and the
    number is Unix seconds, 86400 to a day, not SI seconds. -/
theorem Rfc3339.Spec.siSeconds_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.siSeconds = Rfc3339.Spec.siSeconds t := sorry

/-- On whole seconds, valid by the table, `siSeconds` orders timestamps
    exactly as the instants they name. So no two instants share a
    number, a leap second and the second after it included. -/
theorem Rfc3339.Spec.siSeconds_order (a b : Timestamp) (ha : Rfc3339.Spec.ValidKnown a) (hb : Rfc3339.Spec.ValidKnown b)
    (fa : a.fraction = []) (fb : b.fraction = []) :
    compare a.siSeconds b.siSeconds = a.compareInstant b := sorry

/-- `fromSiSeconds` turns SI seconds since 1972-01-01T00:00:00Z back into
    a timestamp: the one, at most one, in UTC, with no fraction, valid by
    the table and from 1972 on, that has those SI seconds. A leap second
    comes back as second 60. -/
theorem Rfc3339.Spec.fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Rfc3339.Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Rfc3339.Spec.siSeconds t = n := sorry

/-- `fromSiSeconds` gives a timestamp exactly for the seconds from
    1972-01-01T00:00:00Z to 9999-12-31T23:59:59Z. -/
theorem Rfc3339.Spec.fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Rfc3339.Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := sorry

/-- `taiMinusUtc` is 10, and one more for each leap second of the table
    before the timestamp. So during a leap second it is still the value
    from before it. (Before 1972, UTC was not a whole number of seconds
    from TAI, and the 10 there means nothing.) -/
theorem Rfc3339.Spec.taiMinusUtc_leapsBefore (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.taiMinusUtc = 10 + Rfc3339.Spec.leapsBefore t := sorry

/-- TAI − UTC at each second from 1972 on, other than a leap second, is
    the value the table's second column gives for it. The code never
    reads that column: it counts leap seconds. -/
theorem Rfc3339.Spec.taiMinusUtc_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) (h60 : t.second ≠ 60)
    (h72 : Rfc3339.Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ ≤ Rfc3339.Spec.unixSeconds t) :
    t.taiMinusUtc = Rfc3339.Spec.taiMinusUtcAt (Rfc3339.Spec.ntpOfUnix (Rfc3339.Spec.unixSeconds t)) := sorry

/-- The leap seconds of section 5.8, the first and the last of the
    table, one seen from another offset, and second 60 in months that
    had none; SI seconds and TAI − UTC around the first and the last;
    and the round trip that Unix seconds lose and SI seconds keep. -/
theorem Rfc3339.Spec.leap_table_vectors :
    Timestamp.isValidKnown ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = true ∧
    Timestamp.isValidKnown ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨2017, 1, 1, 0, 59, 60, [], .plus 1 0⟩ = true ∧
    Timestamp.isValidKnown ⟨2015, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.isValidKnown ⟨1971, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.isValidKnown ⟨2026, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.siSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 0 ∧
    Timestamp.siSeconds ⟨1972, 6, 30, 23, 59, 59, [], .z⟩ = 15724799 ∧
    Timestamp.siSeconds ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = 15724800 ∧
    Timestamp.siSeconds ⟨1972, 7, 1, 0, 0, 0, [], .z⟩ = 15724801 ∧
    Timestamp.siSeconds ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ = 1420156827 ∧
    Timestamp.siSeconds ⟨2016, 12, 31, 23, 59, 59, [], .z⟩ = 1420156825 ∧
    Timestamp.siSeconds ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = 1420156826 ∧
    Timestamp.taiMinusUtc ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 6, 30, 23, 59, 59, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 7, 1, 0, 0, 0, [], .z⟩ = 11 ∧
    Timestamp.taiMinusUtc ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = 36 ∧
    Timestamp.taiMinusUtc ⟨2016, 12, 31, 23, 59, 59, [], .z⟩ = 36 ∧
    Timestamp.taiMinusUtc ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ = 37 ∧
    fromSiSeconds 15724800 = some ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ ∧
    fromSiSeconds 1420156826 = some ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ ∧
    fromSiSeconds 1420156827 = some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ ∧
    fromUnixSeconds (Timestamp.unixSeconds ⟨2016, 12, 31, 23, 59, 60, [], .z⟩) =
      some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ := sorry

/-! ## RFC 9557: the Internet Extended Date/Time Format -/

/-- `parseExt` returns `e` exactly when `e` is an IXDTF timestamp the
    grammar of section 4.1 allows and the string is how it is written:
    the RFC 3339 part with `T` and `Z` in either case, then the suffix
    as written. So it accepts nothing outside the grammar, rejects
    nothing inside it, and returns the time zone and tags as written. -/
theorem Rfc3339.Spec.parseExt_iff (s : String) (e : Ext) :
    parseExt s = some e ↔
      Rfc3339.Spec.ExtValid e ∧ ∃ dt, s.toList = dt ++ Rfc3339.Spec.renderSuffix e ∧
        dt.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render e.stamp := sorry

/-- An IXDTF timestamp prints as the grammar writes it, with `T` and `Z`
    in upper case. -/
theorem Rfc3339.Spec.printExt_eq (e : Ext) (h : Rfc3339.Spec.ExtValid e) :
    e.print.toList = Rfc3339.Spec.render e.stamp ++ Rfc3339.Spec.renderSuffix e := sorry

/-- Round trip: printing then parsing gives the IXDTF timestamp back. -/
theorem Rfc3339.Spec.parseExt_print (e : Ext) (h : Rfc3339.Spec.ExtValid e) : parseExt e.print = some e := sorry

/-- IXDTF extends RFC 3339: a string with no suffix reads as `parse`
    reads it, with no time zone and no tags. -/
theorem Rfc3339.Spec.parseExt_plain (s : String) (h : '[' ∉ s.toList) :
    parseExt s = (parse s).map fun t => ⟨t, none, []⟩ := sorry

/-- `lookup` gives the first tag with the key, which section 3.3 has an
    application choose when an elective key is repeated. -/
theorem Rfc3339.Spec.lookup_iff (e : Ext) (k : List Char) (t : Tag) :
    e.lookup k = some t ↔ ∃ l r, e.tags = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k := sorry

/-- `erroneous` decides what sections 3.2 to 3.4 make an application
    treat as erroneous. -/
theorem Rfc3339.Spec.erroneous_iff (p : Processor) (e : Ext) :
    e.erroneous p = true ↔ Rfc3339.Spec.MustReject p e := sorry

/-- Every example of RFC 9557, in sections 1.2, 3.3, 3.4 and 4.2, with
    the application of `Rfc3339.Spec.exampleProcessor`: each one is read, and is
    erroneous exactly where the RFC says it must be treated so. Also
    critical time zones that agree with the offset, a critical `-00:00`
    zone that does not, and strings the grammar refuses. -/
theorem Rfc3339.Spec.ixdtf_vectors :
    -- Section 4.2, Figures 4 to 7
    parseExt "1996-12-19T16:39:57-08:00" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none, []⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]), []⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]),
        [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none,
        [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩ ∧
    ((parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some false) ∧
    ((parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some false) ∧
    -- An experiment the application does not take part in
    ((parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some true) ∧
    -- Section 1.2: an offset time zone
    parseExt "2022-07-08T00:14:07+08:45[+08:45]" =
      some ⟨⟨2022, 7, 8, 0, 14, 7, [], .plus 8 45⟩, some (false, .offset (.plus 8 45)), []⟩ ∧
    ((parseExt "2022-07-08T00:14:07+08:45[!+08:45]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    -- Section 3.3, elective: an inconsistent zone, the zones of the note,
    -- an unknown key, repeated keys
    ((parseExt "2022-07-08T00:14:07+01:00[Europe/Paris]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/Paris]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T02:14:07+02:00[Europe/Paris]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07+01:00[knort=blargel]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    -- Section 3.3, critical: the four examples
    ((parseExt "2022-07-08T00:14:07+01:00[!Europe/Paris]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!knort=blargel]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some true) ∧
    -- Section 3.4, Figures 1 and 2
    ((parseExt "2022-07-08T00:14:07+00:00[!Europe/London]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07+00:00[Europe/London]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[!Europe/London]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/London]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    -- Critical zones that agree with the offset, and a critical `-00:00`
    -- zone, offset 0, under an offset of +01:00
    ((parseExt "1996-12-19T16:39:57-08:00[!America/Los_Angeles]").map
      (·.erroneous Rfc3339.Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T02:14:07+02:00[!Europe/Paris]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T01:14:07+01:00[!-00:00]").map (·.erroneous Rfc3339.Spec.exampleProcessor) =
      some true) ∧
    -- `Z` in brackets is a zone name, not an offset
    ((parseExt "2022-07-08T00:14:07Z[Z]").map (·.zone) = some (some (false, .name ["Z".toList]))) ∧
    -- Refused by the grammar: an empty item, `.` and `..`, an upper case
    -- key, an empty value, a time zone after a tag, an offset out of range
    parseExt "2022-07-08T00:14:07Z[]" = none ∧
    parseExt "2022-07-08T00:14:07Z[.]" = none ∧
    parseExt "2022-07-08T00:14:07Z[a/..]" = none ∧
    parseExt "2022-07-08T00:14:07Z[U-ca=x]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=a--b]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=x][Europe/Paris]" = none ∧
    parseExt "2022-07-08T00:14:07Z[+24:00]" = none := sorry
