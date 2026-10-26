# Specification: rfc

This library reads and writes RFC 3339 timestamps, such as `1985-04-12T23:20:50.52Z`. It also gives the instant a timestamp names, as whole seconds since 1970-01-01T00:00:00Z, and puts two timestamps in order by instant. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, `Rfc3339/Types.lean`, and the other files `bar.toml` lists.

## The format

The scope is the `date-time` rule of RFC 3339, section 5.6, with the restrictions of section 5.7:

```
date-time = full-date "T" full-time
full-date = date-fullyear "-" date-month "-" date-mday
full-time = partial-time time-offset
partial-time = time-hour ":" time-minute ":" time-second [time-secfrac]
time-secfrac = "." 1*DIGIT
time-offset = "Z" / ("+" / "-") time-hour ":" time-minute
```

- Every field has exactly the number of digits the grammar gives. A digit is an ASCII digit, `0` to `9`. The parser rejects digits from other scripts, such as `٣` and `０`.
- The year runs from 0000 to 9999 and the month from 01 to 12. The day runs from 01 to the length of its month, as in the table of section 5.7. February has 29 days in a leap year and 28 otherwise. A leap year is one divisible by 4, unless it is divisible by 100 and not by 400 (Appendix C).
- The hour runs from 00 to 23 and the minute from 00 to 59. The second runs from 00 to 59. It may be 60 only for a leap second, which section 5.7 places at the end of a month in UTC. With the offset applied, the time must be 23:59 UTC on the last day of a month. Because the leap second is shifted by the offset, `1990-12-31T15:59:60-08:00` is the same leap second as `1990-12-31T23:59:60Z`.
- Section 5.7 allows second 60 only at the end of months in which a leap second occurs. This library keeps no table of them, so it allows second 60 at the end of every month, which is more than section 5.7 allows. It also allows second 59 everywhere, although section 5.7 makes 58 the last second of a month after a negative leap second, which has never happened. `Spec.Valid` states the rule as this library applies it.
- The fraction is optional. When present it is a point and at least one digit, with no upper limit on the digits. The parser keeps every digit as written.
- The offset is `Z`, `+hh:mm` or `-hh:mm`, with hours from 00 to 23 and minutes from 00 to 59. Section 4.3 gives `-00:00` its own meaning, an unknown local offset. It is therefore kept apart from `+00:00` and from `Z`, although all three name the same instant.
- The note under the grammar lets `T` and `Z` be written in lower case. The parser accepts `t` and `z`, and printing writes upper case.
- The parser reads nothing else. That includes:
  - a space in place of `T`, which section 5.6 lets applications choose;
  - a comma before the fraction;
  - offsets without a colon;
  - a date or time on its own;
  - any other ISO 8601 form;
  - spaces or a line break before or after the timestamp.

## The value

`parse` returns a `Timestamp`: the year, month, day, hour, minute and second as numbers, the fraction as a list of digits, and the offset (`Z`, plus, or minus, with hours and minutes). The fields are those of the string as written, in its local time. `Spec.Valid` says which values the rules above allow. `Timestamp.isValid` decides it for a value built some other way.

`Timestamp.print` writes a valid timestamp in the form above, with `T` and `Z` in upper case.

## Instants

`Timestamp.unixSeconds` gives the whole seconds from 1970-01-01T00:00:00Z to the instant a valid timestamp names, with the offset subtracted, ignoring the fraction. Dates before 1970 give negative numbers. Days are counted in the Gregorian calendar extended back to year 0, which RFC 3339 uses.

POSIX time has no number for a leap second. As in POSIX time, second 60 is counted as 60 seconds into its minute, so `1990-12-31T23:59:60Z` and `1991-01-01T00:00:00Z` give the same number.

`Timestamp.compareInstant` orders two valid timestamps by the instants they name, whatever their offsets: by UTC minute, then by the second within it, where a leap second, 60, comes after 59, then by the fraction, compared exactly. It does not use Unix seconds, so `1990-12-31T23:59:60Z` comes before `1991-01-01T00:00:00Z`. It gives `eq` when the instants are equal, as for `2000-01-01T00:00:00.5Z` and `2000-01-01T01:00:00.500+01:00`.

## From Unix seconds

`fromUnixSeconds` goes the other way: from whole seconds since 1970-01-01T00:00:00Z to the UTC timestamp for that second. Its result is valid, has offset `Z`, no fraction, and a second of at most 59, and names exactly the second it was given. Each second has at most one such timestamp, and when it has one, this is it. A leap second is never a result, since its number is the same as the next second's.

Every second from `0000-01-01T00:00:00Z` (-62167219200) to `9999-12-31T23:59:59Z` (253402300799), the years RFC 3339 allows, has one, and `fromUnixSeconds` returns `none` outside them. So for a valid timestamp `t` whose second is at most 59, `fromUnixSeconds t.unixSeconds` is `t` put into UTC with its fraction dropped, or `none` when that moves it outside those years. A leap second comes back as the second after it, a different instant, so `1990-12-31T23:59:60Z` gives `1991-01-01T00:00:00Z`, and `9999-12-31T23:59:60Z`, at any offset, gives `none`.

## Leap seconds, with the table

Section 5.7 allows second 60 only "at the end of months in which a leap second occurs". `isValid` cannot know those months; `isValidKnown` uses a table of them. The table is tzdata's `leap-seconds.list`, which publishes IERS Bulletin C. `Spec/Leap.lean` copies it line for line: 28 NTP times, from 1 January 1972 to 1 January 2017, each with TAI − UTC from that time on, 10 to 37 seconds. Each line after the first follows a leap second, the second `23:59:60` UTC just before it, so there have been 27. The file expires on 28 June 2027: until then, no leap second comes that it does not list.

- `isValidKnown` is `isValid`, with second 60 allowed only at one of the table's leap seconds. The instant is what counts, whatever the offset: `1990-12-31T15:59:60-08:00` is the leap second at the end of 1990, and `2017-01-01T00:59:60+01:00` the one at the end of 2016. `2015-12-31T23:59:60Z` is refused, since that leap second came at the end of June 2015.
- `siSeconds` gives the SI seconds from `1972-01-01T00:00:00Z`, ignoring the fraction: Unix seconds, and one more for each leap second of the table before the timestamp. So `2016-12-31T23:59:59Z`, `2016-12-31T23:59:60Z` and `2017-01-01T00:00:00Z` get three numbers in a row, where Unix seconds give the last two the same one. On whole seconds valid by the table, these numbers are in the order of the instants, as `compareInstant` gives it.
- `fromSiSeconds` goes back: from SI seconds to the UTC timestamp, a leap second as second 60. It gives one for every number from 0, `1972-01-01T00:00:00Z`, to that of `9999-12-31T23:59:59Z`, and `none` outside.
- `taiMinusUtc` gives TAI − UTC: 10, and one more for each leap second before the timestamp. At every second from 1972 on, a leap second aside, it is the table's second column. During a leap second it is still the value from before it.

Before 1972, UTC ran on seconds of varying length, so these numbers mean nothing there, and no statement covers them. A leap second announced after the table's date would need a new table, in the spec and in the code, and a new approval.

## Errors

`parse` returns `none` for any string it does not accept, `fromUnixSeconds` for any number outside the years 0000 to 9999, and `fromSiSeconds` for any number outside 1972 to 9999. No function can fail any other way.

## The command-line tool

The command-line tool in `Main.lean` has two modes:

- `rfc3339 check TIMESTAMP...` prints each timestamp's printed form and its Unix seconds, or `invalid`. It exits with 1 when any timestamp is invalid.
- `rfc3339 serve` answers requests from the differential tests, one per line. Each string is sent as the hex digits of its UTF-8 bytes. The header comment of `Main.lean` gives the protocol.

Every answer comes from `parse`, `Timestamp.print`, `Timestamp.unixSeconds`, `Timestamp.compareInstant`, `fromUnixSeconds`, `Timestamp.isValidKnown`, `Timestamp.siSeconds`, `Timestamp.taiMinusUtc` and `fromSiSeconds`. The `known` request prints `-` for TAI − UTC before 1972.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use are in `Spec/Defs.lean` and, for the leap second table, `Spec/Leap.lean`. They are written from the RFC and checked against its tables and against known day counts.

| Property | Theorem |
|----------|---------|
| `isValid` decides exactly `Spec.Valid`: the rules of sections 5.6 and 5.7, with second 60 allowed at the end of every month. | `Spec.isValid_iff` |
| A valid timestamp prints as the grammar writes it. | `Spec.print_eq` |
| `parse` returns `t` exactly when `t` is valid and the string is how `t` prints, with `T` and `Z` in either case. | `Spec.parse_iff` |
| What `parse` returns is valid: the day exists in its month, a leap second ends a month in UTC, and so on. | `Spec.parse_valid` |
| Printing then parsing gives the timestamp back. | `Spec.parse_print` |
| Parsing then printing gives the string back, with `T` and `Z` in upper case. | `Spec.print_parse` |
| `unixSeconds` counts the seconds from the epoch by the calendar, with the offset applied. | `Spec.unixSeconds_eq` |
| `compareInstant` orders timestamps by the instants they name: UTC minute, then second, then fraction. | `Spec.compareInstant_eq` |
| The examples of section 5.8 parse to the fields the RFC reads them as. | `Spec.rfc3339_examples` |
| What section 5.8 says about those examples holds: two pairs name the same instant. Separately, the first is 482196050 seconds after the epoch, as Python's `calendar.timegm` gives. | `Spec.rfc3339_example_instants` |
| A leap second comes after second 59 and before the next minute; its Unix seconds equal those of the next second. | `Spec.leap_second_order` |
| Days outside their month are rejected, with the leap year rule of Appendix C. | `Spec.calendar_vectors` |
| Second 60 is accepted only at the end of a month in UTC. | `Spec.leap_second_vectors` |
| Lower case `t` and `z` are read; a space for `T`, a missing part, a comma, an out-of-range offset and trailing text are not. | `Spec.syntax_vectors` |
| `fromUnixSeconds s` is `t` exactly when `t` is valid, in UTC, with no fraction and a second of at most 59, and names `s`. | `Spec.fromUnixSeconds_iff` |
| `fromUnixSeconds` gives a timestamp exactly for the seconds from 0000-01-01T00:00:00Z to 9999-12-31T23:59:59Z. | `Spec.fromUnixSeconds_isSome` |
| The epoch, the section 5.8 example, a leap day, the last second of a signed 32-bit count, the second before the epoch, and the ends of the range and one second past each. | `Spec.fromUnixSeconds_vectors` |
| `isValidKnown` decides `Spec.ValidKnown`: `Spec.Valid`, with second 60 only at a leap second of the table. | `Spec.isValidKnown_iff` |
| `siSeconds` is Unix seconds since 1972 and one more for each leap second of the table before the timestamp. | `Spec.siSeconds_eq` |
| On whole seconds valid by the table, `siSeconds` gives the order of the instants. | `Spec.siSeconds_order` |
| `fromSiSeconds n` is `t` exactly when `t` is in UTC, with no fraction, valid by the table, from 1972 on, and has SI seconds `n`; it gives one for every second from 1972 to 9999. | `Spec.fromSiSeconds_iff`, `Spec.fromSiSeconds_isSome` |
| TAI − UTC from 1972 on, at each second but a leap second, is the table's value. | `Spec.taiMinusUtc_eq` |
| Leap seconds of the table and months without one; SI seconds and TAI − UTC around the first and the last; the round trip Unix seconds lose. | `Spec.leap_table_vectors` |

Together, these fix every output for valid input.

- `parse` is fixed for every string.
- `print`, `unixSeconds` and `compareInstant` are fixed for every valid timestamp. The parser gives only valid timestamps.
- `fromUnixSeconds` is fixed for every number, by `Spec.fromUnixSeconds_iff` and `Spec.fromUnixSeconds_isSome`, and `fromSiSeconds` likewise by its two statements.
- `isValidKnown` is fixed for every timestamp, and `siSeconds` for every valid one. `taiMinusUtc` is fixed for every valid timestamp from 1972 on but a leap second.
- A parser that accepted nothing would meet `Spec.parse_valid`, but it would fail `Spec.parse_iff` and `Spec.parse_print`.
- A parser that accepted too much would fail `Spec.parse_iff`.

## Oracle

The differential tests compare the tool with two oracles:

- Python's `datetime` and `calendar` modules: month lengths, offset arithmetic, seconds since the epoch, `datetime.fromisoformat` on every accepted string it can hold, and the UTC timestamp for a number of seconds. `datetime` holds no year 0, so dates there are moved by 400 years, one cycle of the Gregorian calendar, for the arithmetic.
- A copy of the rules above, written in Python from the RFC.
- For leap seconds, tzdata's `leap-seconds.list` on the test machine, read by the test script itself, with the SI seconds and TAI − UTC worked out from it in Python.
