# rfc: RFC 3339 timestamps, proved

This library reads, checks and writes RFC 3339 timestamps, such as `1985-04-12T23:20:50.52Z`, in Lean. Machine-checked proofs show that it accepts exactly the strings that the RFC's grammar and calendar rules allow, including the day ranges and leap years of the calendar. `isValid` has one relaxation: it accepts a leap second at the end of any month. `isValidKnown` is exact: it checks second 60 against the table of the 27 leap seconds there have been, as tzdata publishes it. The proofs also cover the round trip from text to value and back, the count of seconds since the Unix epoch, and the order of two timestamps by the instant they name. A count of SI seconds since 1972 gives each leap second its own number, so a round trip through it keeps a leap second, as one through Unix seconds cannot. TAI − UTC is also given, as 10 plus the leap seconds before the timestamp, and proved to agree with the table's own TAI − UTC column at every second from 1972 on but a leap second. It also reads and writes the extended form of RFC 9557, which adds a time zone and tagged values after the timestamp, as in `1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]`. The proofs show that it accepts exactly that grammar, with RFC 3339 timestamps as `parse` reads them, and that it decides which strings an application must treat as erroneous by sections 3.2 to 3.4, given what the application can process. The library is tested against Python's date and time code and a Python copy of the RFC 9557 grammar; `tests/TEST-RESULTS.md` has the record.

It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

```
lake build
.lake/build/bin/rfc3339 check 1985-04-12T23:20:50.52Z 2001-02-29T00:00:00Z
```

For each timestamp it prints the timestamp as written, with `T` and `Z` in upper case, and its Unix seconds. A timestamp the RFC does not allow prints `invalid`, and the tool then exits with 1. From Lean, the functions are these:

- `Rfc3339.parse`
- `Timestamp.print`
- `Timestamp.isValid`
- `Timestamp.unixSeconds`
- `Timestamp.compareInstant`
- `Rfc3339.fromUnixSeconds`
- `Timestamp.isValidKnown`
- `Timestamp.siSeconds`
- `Timestamp.taiMinusUtc`
- `Rfc3339.fromSiSeconds`
- `Rfc3339.parseExt`
- `Ext.print`
- `Ext.lookup`
- `Ext.erroneous`

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`. The definitions they use, written from the RFC, are in `Spec/Defs.lean`; those for the leap second table, with the table itself, are in `Spec/Leap.lean`; those for RFC 9557, with its grammar, are in `Spec/Ixdtf.lean`; and the types are in `Rfc3339/Types.lean` and `Rfc3339/IxdtfTypes.lean`. The proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| `isValid` decides the rules of RFC 3339, sections 5.6 and 5.7. Every field is in its range. The day exists in its month, with the leap years of Appendix C. Second 60 falls only at 23:59 UTC on the last day of a month. Section 5.7 allows it only in months that had a leap second; `isValid` uses no table of them, so any month is accepted. | `Spec.isValid_iff` |
| A valid timestamp prints as the grammar of section 5.6 writes it, with `T` and `Z` in upper case. | `Spec.print_eq` |
| `parse` returns a timestamp exactly when the timestamp is valid and the string is how it prints, with `T` and `Z` in either case. So `parse` accepts nothing outside the grammar and those rules, rejects nothing inside them, and returns the fields as written. | `Spec.parse_iff` |
| What `parse` returns is valid; for example, 30 February never passes. | `Spec.parse_valid` |
| Printing then parsing gives the timestamp back. | `Spec.parse_print` |
| Parsing then printing gives the string back, with `T` and `Z` in upper case. | `Spec.print_parse` |
| `unixSeconds` counts the whole seconds from 1970-01-01T00:00:00Z, with the offset applied. Its fast day arithmetic equals a day count that adds up month and year lengths. | `Spec.unixSeconds_eq` |
| `compareInstant` orders two timestamps by the instants they name, whatever their offsets: by UTC minute, then by the second within it, where a leap second comes after 59, then by the fraction, compared exactly. | `Spec.compareInstant_eq` |
| The examples of section 5.8 parse to the fields the RFC gives. What the RFC says about them holds: `1996-12-19T16:39:57-08:00` is the instant `1996-12-20T00:39:57Z`, and `1990-12-31T15:59:60-08:00` is the same leap second as `1990-12-31T23:59:60Z`. Separately, `1985-04-12T23:20:50.52Z` is 482196050 seconds after the epoch, as Python's `calendar.timegm` also gives. | `Spec.rfc3339_examples`, `Spec.rfc3339_example_instants` |
| A leap second comes after second 59 and before the next minute, fraction included. Its Unix seconds equal those of the second after it. | `Spec.leap_second_order` |
| `fromUnixSeconds` turns whole seconds since the epoch back into a timestamp: the one, at most one, that is valid, in UTC, with no fraction and no leap second, and names those seconds. Its date arithmetic is checked against the same day count. | `Spec.fromUnixSeconds_iff` |
| `fromUnixSeconds` gives a timestamp exactly for the seconds from 0000-01-01T00:00:00Z to 9999-12-31T23:59:59Z, and `none` outside them. | `Spec.fromUnixSeconds_isSome` |
| `fromUnixSeconds` gives the epoch, the section 5.8 example, 2000-02-29, 2038-01-19T03:14:07Z for the last second of a signed 32-bit count, the second before the epoch, and both ends of the range, and gives `none` one second past each end. | `Spec.fromUnixSeconds_vectors` |
| The calendar, leap second, and syntax cases: 29 February in 1900, 2000 and 2001; second 60 at and away from a month's end; lower case `t` and `z`; a space for `T`; a comma; an offset of `+24:00`; trailing text. | `Spec.calendar_vectors`, `Spec.leap_second_vectors`, `Spec.syntax_vectors` |
| `isValidKnown` decides section 5.7 with the table of leap seconds. It allows second 60 only at one of the table's leap seconds, at the same instant whatever the offset. The table is the one in `Spec/Leap.lean`. The code keeps its own list of months. The lemma `Rfc3339.Proofs.Leap.leapKey_table`, in `Proofs/Leap/Table.lean`, shows that the list gives the table's leap seconds, in order. | `Spec.isValidKnown_iff` |
| `siSeconds` is the Unix seconds since 1972-01-01T00:00:00Z, and one more for each leap second of the table before the timestamp. From 1972 on, those are the SI seconds; so a leap second, the second before it and the second after it get three numbers in a row. Before 1972 the number is Unix seconds, 86400 to a day. | `Spec.siSeconds_eq` |
| On whole seconds valid by the table, `siSeconds` orders timestamps exactly as `compareInstant` does. So no two instants share a number, a leap second and the second after it included. | `Spec.siSeconds_order` |
| `fromSiSeconds` turns SI seconds back into the one UTC timestamp from 1972 on, valid by the table, that has them, a leap second included. It gives a timestamp for every second from 1972-01-01T00:00:00Z to 9999-12-31T23:59:59Z and `none` outside. | `Spec.fromSiSeconds_iff`, `Spec.fromSiSeconds_isSome` |
| `taiMinusUtc` is 10, and one more for each leap second of the table before the timestamp, so during a leap second it is still the value from before it. | `Spec.taiMinusUtc_leapsBefore` |
| TAI − UTC at each second from 1972 on, other than a leap second, is the value in the table's second column, 10 to 37. The code never reads that column; it counts leap seconds. | `Spec.taiMinusUtc_eq` |
| Section 5.8's leap seconds, the table's first and last, one seen from another offset, and second 60 in months that had none. SI seconds and TAI − UTC around the first and the last leap second. And the round trip that Unix seconds lose and SI seconds keep. | `Spec.leap_table_vectors` |
| `parseExt` reads exactly the strings of RFC 9557's `date-time-ext` rule, with one relaxation: an RFC 3339 timestamp, as `parse` reads it, so with second 60 at the end of any month, then a time zone, a name or a numeric offset, if there is one, and the tags, each perhaps marked critical with `!`. It returns the timestamp, the zone and the tags as written. | `Spec.parseExt_iff` |
| A valid IXDTF timestamp prints as the grammar writes it, and printing then parsing gives it back. | `Spec.printExt_eq`, `Spec.parseExt_print` |
| A string with no suffix reads as `parse` reads it, with no time zone and no tags. | `Spec.parseExt_plain` |
| `lookup` gives the first tag with a key, which section 3.3 has an application choose when an elective key is repeated. | `Spec.lookup_iff` |
| `erroneous` decides what sections 3.2 to 3.4 make an application treat as erroneous, for an application described by the tags it processes and the zone offsets it knows: a critical time zone it does not know or that disagrees with the offset, a critical tag it cannot process or whose key is repeated with other values, and an experimental key, one starting with `_`, it does not take part in. | `Spec.erroneous_iff` |
| Every example of RFC 9557, in sections 1.2, 3.3, 3.4 and 4.2, read and judged by an example application, as the RFC judges them. Critical time zones that agree with the offset, a critical `-00:00` zone that does not, and `[Z]` read as a zone name. Strings the grammar refuses: an empty item, `.` and `..` as zone parts, an upper case key, an empty value, a time zone after a tag, and an offset out of range. | `Spec.ixdtf_vectors` |

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: the hex decoding and UTF-8 check in `serve` mode, the arguments, output and exit codes of `check` mode, the decimal printing of numbers and reading of the numbers `fromunix` and `fromsi` take, the layout of the `known` answer, with `-` for TAI − UTC before 1972, and the layout of the `ixdtf` answer, which judges each string with the example application of `Spec.exampleProcessor`. The differential tests cover them, with malformed requests and CR LF line endings.
- Whether a leap second was announced, in `isValid`, `parse` and `parseExt`. They accept second 60 at 23:59 UTC at the end of any month, where section 5.7 allows it only at the end of months in which a leap second occurs; `isValidKnown` checks that against the table. Second 59 is always accepted, although section 5.7 makes 58 the last second of a month after a negative leap second, which has never happened.
- The table after its expiry date, 28 June 2027. `isValidKnown` refuses second 60 at any month end the table does not list, and `siSeconds` and `taiMinusUtc` count no leap second after 2016. If one is ever announced, the table in the spec and the code's list must change together, and the spec approved again. The table is what tzdata publishes from IERS Bulletin C; that it matches the IERS record is trusted, not proved.
- SI seconds and TAI − UTC before 1972. UTC then ran on seconds of varying length, with TAI − UTC not a whole number of seconds. Before 1972, `Spec.siSeconds_eq` makes `siSeconds` Unix seconds less 63072000, 86400 to a day, which are not SI seconds there, and `taiMinusUtc` gives 10, which means nothing there; the tool's `known` request prints `-` for TAI − UTC.
- The table itself. `Spec/Leap.lean` copies tzdata's `leap-seconds.list` (tzdata 2026e, updated through IERS Bulletin C, expiring 28 June 2027) line for line. That copy is part of the specification: the reviewer checks it against the file, and the differential tests check the code against the copy of the file on the test machine, but no proof does. "Refresh the leap second table", below, says how to update the copy.
- Unix seconds at a leap second. They count second 60 as the first second of the next minute, as POSIX time does, so a leap second and the second after it give the same number. `compareInstant` does not use them, and puts the leap second first. `fromUnixSeconds` turns that number into the second after the leap second, so a round trip through Unix seconds loses a leap second, and `9999-12-31T23:59:60Z` gives `none`.
- Time zone rules. `parseExt` reads a time zone name by the grammar, but this library holds no time zone database: it does not know whether `Europe/Paris` exists or what its offset is. `erroneous` asks the application, through its `Processor`, for the offset a named zone has at an instant, and which tags it can process. What the application does with a tag, such as a calendar, is its own.
- The tool's `ixdtf` answer for any application but the example one. The tool judges every string with the example application of `Spec.exampleProcessor`, and with no other. `Spec.ixdtf_vectors` judges the RFC's examples with it, and the tests use it too, since they need a fixed one. It knows three zones. Each has one fixed offset, whatever the instant: Europe/Paris `+02:00`, Europe/London `+01:00` and America/Los_Angeles `-08:00`. These are their offsets at the instants of the RFC's examples in sections 3.3, 3.4 and 4.2: July 2022 for Paris and London, December 1996 for Los Angeles. So the tool judges `2022-01-08T00:14:07+01:00[!Europe/Paris]` erroneous, although Paris is at `+01:00` in January. A real application passes its own `Processor` to `Ext.erroneous`.
- RFC 9557's `time-zone` rule read literally. In ABNF, alternation binds more loosely than concatenation, so the rule as written reads `("[" critical-flag time-zone-name) / (time-numoffset "]")`. `Spec/Ixdtf.lean` follows the intent, which the RFC's note and every example show: a name or an offset between the brackets.
- Forms outside RFC 3339 and RFC 9557 are not supported, by design:
  - a space in place of `T`, which section 5.6 lets applications choose;
  - other ISO 8601 forms, such as an offset with no colon in a time zone suffix;
  - years outside 0000 to 9999.
- Speed. The code works on lists of characters, which suits proofs, not bulk data.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers and integers and the conversion between strings and lists of characters.
- The operating system and hardware it runs on.
- Python's `datetime` and `calendar` modules, and for leap seconds the copy of tzdata's `leap-seconds.list` on the test machine, as oracles in the differential tests. The record names the Python version and the file.

This project has no dependencies beyond Lean itself.

## Other parsers

`tests/CROSS-CHECK.md` records a one-off comparison with Go's `time.Parse` and with `rfc3339-validator`. That package is the one the Python `jsonschema` package calls for its `date-time` check, after upper-casing the string. The comparison is not part of the verified bar. The differences it found:

- Both reject lower case `t` and `z`, which section 5.6 allows, and second 60. jsonschema upper-cases the string first, so it does accept lower case.
- `rfc3339-validator` rejects year 0000; Go accepts it.
- Go accepts offsets such as `+24:00` and `+23:60`.
- Go accepts fields with one digit, such as `T0:44:28`.
- Go accepts a comma before the fraction.
- `rfc3339-validator` accepts a timestamp followed by a line break.

For RFC 9557, it compares `parseExt` with `Temporal.Instant.from` in Node's built-in Temporal, which is behind a flag and older than the current proposal. This Temporal refuses every critical flag, even on an item it acts on. It also refuses experimental and unknown keys, a repeated `u-ca`, and fractions finer than nanoseconds. Its older grammar also refuses a calendar with a part outside 3 to 8 characters, and a time zone name with a digit or `+`, other than the `Etc/GMT` forms, or with a part over 14 characters. It reads calendars and zone names it does not know. It accepts a few strings this project refuses, as RFC 9557 does, such as a zone offset with no colon and a stray `]`.

For leap seconds, it compares `siSeconds`, `taiMinusUtc` and `fromSiSeconds` with ERFA, a BSD-licensed C library derived from the IAU's SOFA, through pyerfa, which keeps its own leap second table. `tests/CROSS-CHECK.md` gives the counts.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), Python 3.11 or later, and tzdata, for `/usr/share/zoneinfo/leap-seconds.list`.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script compares the tool with Python's `datetime` and `calendar` modules, with the RFC's rules copied into the script, and with tzdata's `leap-seconds.list`, which the script reads itself, on inputs from a recorded seed. It then rewrites `tests/TEST-RESULTS.md`.

## Refresh the leap second table

The table in `Spec/Leap.lean` is tzdata 2026e's `leap-seconds.list`, which expires on 28 June 2027. Look for a new file each time IERS publishes a new Bulletin C, and before the expiry date. To refresh the table from a new file:

1. In `Spec/Leap.lean`, copy the tzdata release and the file's `#$` stamp, `#h` hash and expiry lines into the comment. Copy any new data line into the comment's table and into `Spec.leapTable`.
2. For each new leap second, add its (year, month) to `leapMonths` in `Rfc3339/Leap.lean`.
3. Change the tzdata release and the expiry date wherever the text gives them: `Spec/Leap.lean`, `Rfc3339/Leap.lean`, `SPEC.md` and this page. After a new leap second, also change the counts and the last leap second where the text names them, as in `SPEC.md`'s "Leap seconds, with the table".
4. On a machine whose tzdata has the new file, run `lake build`, `lake comparator --paranoid` and `python3 tests/run_tests.py`. The tests read that machine's file, so they check the code against the new table. After a new leap second, some proofs in `Proofs/Leap/` name the count of 27, the last leap second, or the SI seconds of `9999-12-31T23:59:59Z`, and need the new values.
5. The spec files have changed, so the spec needs a new approval.

The code does not read the expiry date or the clock. After 28 June 2027 it answers as before, as if no leap second came after 2016: `isValidKnown` refuses second 60 at the end of every later month, and `taiMinusUtc` stays 37.

## Layout

- `Rfc3339/Types.lean`: the timestamp and offset types. It is part of the specification.
- `Rfc3339/IxdtfTypes.lean`: the RFC 9557 types, the time zone, the tags, and what an application can process. It is part of the specification.
- `Rfc3339/Calendar.lean`, `Rfc3339/Format.lean`, `Rfc3339/Instant.lean`, `Rfc3339/FromUnix.lean`, `Rfc3339/Leap.lean`, `Rfc3339/Ixdtf.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the RFC, with checks against its tables and known day counts.
- `Spec/Leap.lean`: the leap second table, line for line from tzdata's `leap-seconds.list`, and the definitions the leap second statements use.
- `Spec/Ixdtf.lean`: RFC 9557's grammar, the rules for what an application must reject, and the example application.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/cross_check.py`, `tests/cross_check/main.go` and `tests/cross_check/ixdtf.js`: the one-off comparison with other parsers, with ERFA for leap seconds, and with Temporal for RFC 9557.
