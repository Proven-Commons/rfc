# rfc: RFC 3339 timestamps, proved

This library reads, checks and writes RFC 3339 timestamps, such as `1985-04-12T23:20:50.52Z`, in Lean. Machine-checked proofs show that it accepts exactly what the RFC allows. That includes the day ranges and leap years of the calendar and the rule for leap seconds. The proofs also cover the round trip from text to value and back, the count of seconds since the Unix epoch, and the order of two timestamps by the instant they name. The library is tested against Python's date and time code; `tests/TEST-RESULTS.md` has the record.

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

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`. The definitions they use, written from the RFC, are in `Spec/Defs.lean`, and the types are in `Rfc3339/Types.lean`. The proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| `isValid` decides exactly the rules of RFC 3339, sections 5.6 and 5.7. Every field is in its range. The day exists in its month, with the leap years of Appendix C. Second 60 falls only at 23:59 UTC on the last day of a month. | `Spec.isValid_iff` |
| A valid timestamp prints as the grammar of section 5.6 writes it, with `T` and `Z` in upper case. | `Spec.print_eq` |
| `parse` returns a timestamp exactly when the timestamp is valid and the string is how it prints, with `T` and `Z` in either case. So `parse` accepts nothing outside the RFC's grammar and rules, rejects nothing inside them, and returns the fields as written. | `Spec.parse_iff` |
| What `parse` returns is valid; for example, 30 February never passes. | `Spec.parse_valid` |
| Printing then parsing gives the timestamp back. | `Spec.parse_print` |
| Parsing then printing gives the string back, with `T` and `Z` in upper case. | `Spec.print_parse` |
| `unixSeconds` counts the whole seconds from 1970-01-01T00:00:00Z, with the offset applied. Its fast day arithmetic equals a day count that adds up month and year lengths. | `Spec.unixSeconds_eq` |
| `compareInstant` orders two timestamps by the exact instants they name, fraction included, whatever their offsets. | `Spec.compareInstant_eq` |
| The examples of section 5.8 parse to the fields the RFC gives. What the RFC says about them holds: `1996-12-19T16:39:57-08:00` is the instant `1996-12-20T00:39:57Z`, and `1990-12-31T15:59:60-08:00` is the same leap second as `1990-12-31T23:59:60Z`. | `Spec.rfc3339_examples`, `Spec.rfc3339_example_instants` |
| The calendar, leap second, and syntax cases: 29 February in 1900, 2000 and 2001; second 60 at and away from a month's end; lower case `t` and `z`; a space for `T`; a comma; an offset of `+24:00`; trailing text. | `Spec.calendar_vectors`, `Spec.leap_second_vectors`, `Spec.syntax_vectors` |

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: the command-line arguments, the hex decoding and UTF-8 check in `serve` mode, and the decimal printing of numbers. The differential tests cover them, malformed requests included.
- Whether a leap second was announced. Second 60 is accepted at the end of any month in UTC, as section 5.7 allows, without a table of leap seconds. Second 59 is always accepted, although after a negative leap second, which has never happened, the last second of the month would be 58.
- What happens at a leap second. Seconds since the epoch count second 60 as the first second of the next minute, as POSIX time does, so a leap second and the second after it give the same number and compare as the same instant.
- Forms outside RFC 3339 are not supported, by design:
  - a space in place of `T`, which section 5.6 lets applications choose;
  - other ISO 8601 forms;
  - named time zones;
  - years outside 0000 to 9999.
- Speed. The code works on lists of characters, which suits proofs, not bulk data.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers and integers and the conversion between strings and lists of characters.
- The operating system and hardware it runs on.
- Python's `datetime` and `calendar` modules, as an oracle in the differential tests. The record names the Python version.

This project has no dependencies beyond Lean itself.

## Other parsers

`tests/CROSS-CHECK.md` records a one-off comparison with Go's `time.Parse` and with `rfc3339-validator`, the `date-time` check used by the Python `jsonschema` package. It is not part of the verified bar. The differences it found, other than lower case `t` and `z`, leap seconds and year 0000, which both reject:

- Go accepts offsets such as `+24:00` and `+23:60`.
- Go accepts fields with one digit, such as `T0:44:28`.
- Go accepts a comma before the fraction.
- `rfc3339-validator` accepts a timestamp followed by a line break.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.11 or later.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script compares the tool with Python's `datetime` and `calendar` modules, and with the RFC's rules copied into the script, on inputs from a recorded seed. It then rewrites `tests/TEST-RESULTS.md`.

## Layout

- `Rfc3339/Types.lean`: the timestamp and offset types. It is part of the specification.
- `Rfc3339/Calendar.lean`, `Rfc3339/Format.lean`, `Rfc3339/Instant.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the RFC, with checks against its tables and known day counts.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/cross_check.py` and `tests/cross_check/main.go`: the one-off comparison with other parsers.
