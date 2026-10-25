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

/-- `isValid` decides exactly the rules of sections 5.6 and 5.7. -/
theorem Spec.isValid_iff (t : Timestamp) : t.isValid = true ↔ Spec.Valid t := sorry

/-! ## Printing -/

/-- A valid timestamp prints as the grammar of section 5.6 writes it,
    with `T` and `Z` in upper case. -/
theorem Spec.print_eq (t : Timestamp) (h : Spec.Valid t) :
    t.print.toList = Spec.render t := sorry

/-! ## Parsing -/

/-- `parse` returns `t` exactly when `t` is valid and the string is how
    `t` is written, with `T` and `Z` in either case. So it accepts
    nothing outside the grammar and rules of RFC 3339, rejects nothing
    inside them, and returns the fields as written. -/
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

/-- `compareInstant` orders two timestamps by the exact instants they
    name, fraction included. -/
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
    to 1996-12-20T00:39:57Z", the fourth is "the same leap second" as the
    third, and the first is 482196050 seconds after the epoch. -/
theorem Spec.rfc3339_example_instants :
    (Timestamp.compareInstant ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩
      ⟨1996, 12, 20, 0, 39, 57, [], .z⟩ = .eq) ∧
    (Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = .eq) ∧
    Timestamp.unixSeconds ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ = 482196050 := sorry

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
