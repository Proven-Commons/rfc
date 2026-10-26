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
import Spec.Leap
import Spec.Ixdtf

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

/-! ## Leap seconds, with the table -/

/-- `isValidKnown` decides section 5.7 with the table of leap seconds:
    as `isValid`, but second 60 only at one of the table's leap seconds,
    at the same instant whatever the offset. -/
theorem Spec.isValidKnown_iff (t : Timestamp) :
    t.isValidKnown = true ↔ Spec.ValidKnown t := sorry

/-- `siSeconds` is the Unix seconds from 1972-01-01T00:00:00Z to the
    timestamp, leaving out the fraction, and one more for each leap
    second of the table before it. From 1972 on, those are the SI
    seconds between them; before 1972 there are no leap seconds, and the
    number is Unix seconds, 86400 to a day, not SI seconds. -/
theorem Spec.siSeconds_eq (t : Timestamp) (h : Spec.Valid t) :
    t.siSeconds = Spec.siSeconds t := sorry

/-- On whole seconds, valid by the table, `siSeconds` orders timestamps
    exactly as the instants they name. So no two instants share a
    number, a leap second and the second after it included. -/
theorem Spec.siSeconds_order (a b : Timestamp) (ha : Spec.ValidKnown a) (hb : Spec.ValidKnown b)
    (fa : a.fraction = []) (fb : b.fraction = []) :
    compare a.siSeconds b.siSeconds = a.compareInstant b := sorry

/-- `fromSiSeconds` turns SI seconds since 1972-01-01T00:00:00Z back into
    a timestamp: the one, at most one, in UTC, with no fraction, valid by
    the table and from 1972 on, that has those SI seconds. A leap second
    comes back as second 60. -/
theorem Spec.fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Spec.siSeconds t = n := sorry

/-- `fromSiSeconds` gives a timestamp exactly for the seconds from
    1972-01-01T00:00:00Z to 9999-12-31T23:59:59Z. -/
theorem Spec.fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := sorry

/-- `taiMinusUtc` is 10, and one more for each leap second of the table
    before the timestamp. So during a leap second it is still the value
    from before it. (Before 1972, UTC was not a whole number of seconds
    from TAI, and the 10 there means nothing.) -/
theorem Spec.taiMinusUtc_leapsBefore (t : Timestamp) (h : Spec.Valid t) :
    t.taiMinusUtc = 10 + Spec.leapsBefore t := sorry

/-- TAI − UTC at each second from 1972 on, other than a leap second, is
    the value the table's second column gives for it. The code never
    reads that column: it counts leap seconds. -/
theorem Spec.taiMinusUtc_eq (t : Timestamp) (h : Spec.Valid t) (h60 : t.second ≠ 60)
    (h72 : Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ ≤ Spec.unixSeconds t) :
    t.taiMinusUtc = Spec.taiMinusUtcAt (Spec.ntpOfUnix (Spec.unixSeconds t)) := sorry

/-- The leap seconds of section 5.8, the first and the last of the
    table, one seen from another offset, and second 60 in months that
    had none; SI seconds and TAI − UTC around the first and the last;
    and the round trip that Unix seconds lose and SI seconds keep. -/
theorem Spec.leap_table_vectors :
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
theorem Spec.parseExt_iff (s : String) (e : Ext) :
    parseExt s = some e ↔
      Spec.ExtValid e ∧ ∃ dt, s.toList = dt ++ Spec.renderSuffix e ∧
        dt.map Spec.asciiUpper = Spec.render e.stamp := sorry

/-- An IXDTF timestamp prints as the grammar writes it, with `T` and `Z`
    in upper case. -/
theorem Spec.printExt_eq (e : Ext) (h : Spec.ExtValid e) :
    e.print.toList = Spec.render e.stamp ++ Spec.renderSuffix e := sorry

/-- Round trip: printing then parsing gives the IXDTF timestamp back. -/
theorem Spec.parseExt_print (e : Ext) (h : Spec.ExtValid e) : parseExt e.print = some e := sorry

/-- IXDTF extends RFC 3339: a string with no suffix reads as `parse`
    reads it, with no time zone and no tags. -/
theorem Spec.parseExt_plain (s : String) (h : '[' ∉ s.toList) :
    parseExt s = (parse s).map fun t => ⟨t, none, []⟩ := sorry

/-- `lookup` gives the first tag with the key, which section 3.3 has an
    application choose when an elective key is repeated. -/
theorem Spec.lookup_iff (e : Ext) (k : List Char) (t : Tag) :
    e.lookup k = some t ↔ ∃ l r, e.tags = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k := sorry

/-- `erroneous` decides what sections 3.2 to 3.4 make an application
    treat as erroneous. -/
theorem Spec.erroneous_iff (p : Processor) (e : Ext) :
    e.erroneous p = true ↔ Spec.MustReject p e := sorry

/-- The examples of sections 3.3, 3.4 and 4.2, with the application of
    `Spec.exampleProcessor`: each one is read, and is erroneous exactly
    where the RFC says it must be treated so. And strings the grammar
    refuses. -/
theorem Spec.ixdtf_vectors :
    (parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]),
        [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩) ∧
    (parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none,
        [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩) ∧
    -- Elective: an inconsistent zone, an unknown key, repeated keys
    ((parseExt "2022-07-08T00:14:07+01:00[Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07+01:00[knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    -- Critical: the four of section 3.3
    ((parseExt "2022-07-08T00:14:07+01:00[!Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    -- Figures 1 and 2 of section 3.4
    ((parseExt "2022-07-08T00:14:07+00:00[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07+00:00[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    -- An experiment the application does not take part in
    ((parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    -- Refused by the grammar: an empty item, `.` and `..`, an upper case
    -- key, an empty value, a time zone after a tag, `Z` as an offset
    -- (it reads as a zone name), an offset out of range
    parseExt "2022-07-08T00:14:07Z[]" = none ∧
    parseExt "2022-07-08T00:14:07Z[.]" = none ∧
    parseExt "2022-07-08T00:14:07Z[a/..]" = none ∧
    parseExt "2022-07-08T00:14:07Z[U-ca=x]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=a--b]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=x][Europe/Paris]" = none ∧
    parseExt "2022-07-08T00:14:07Z[+24:00]" = none := sorry
