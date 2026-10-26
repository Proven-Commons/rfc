# Cross-check with other parsers

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- This project: the `rfc3339` tool, as tested in TEST-RESULTS.md
- Go: `time.Parse(time.RFC3339Nano, s)`, go version go1.24.7 linux/amd64
- rfc3339-validator 0.1.4 (Python 3.13.17), called on the string as given. `jsonschema` calls it for its `date-time` check on the upper-cased string, so the lower case rows below do not apply to `jsonschema`.
- Seed: 20261025
- Strings: 182155
- Strings both this project and Go accept, read to a different instant: 0

Where each parser differs from this one, by the first category that fits the string:

| Parser | Differs by | Category | Strings | Example |
| --- | --- | --- | --- | --- |
| Go | rejects | lower case t or z | 18967 | `'1985-04-12t23:20:50.52z'`, `'2100-10-31t02:52:09+00:50'` |
| Go | rejects | second 60 | 3783 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| Go | accepts | offset hour above 23 or minute above 59 | 1978 | `'2000-01-01T00:00:00+24:00'`, `'2000-01-01T00:00:00+23:60'` |
| Go | accepts | a field with one digit | 448 | `'0099-09-29T8:05:14.9-13:23'`, `'0508-04-01T2:41:06.3-08:38'` |
| Go | accepts | comma before the fraction | 4 | `'2000-01-01T00:00:00,5Z'`, `'1900-01-02T22:19:55,9-00:00'` |
| rfc3339-validator | rejects | lower case t or z | 18967 | `'1985-04-12t23:20:50.52z'`, `'2100-10-31t02:52:09+00:50'` |
| rfc3339-validator | rejects | second 60 | 3783 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| rfc3339-validator | rejects | year 0000 | 1248 | `'0000-01-01T00:00:00Z'`, `'0000-01-01T12:00:00Z'` |
| rfc3339-validator | accepts | line break at the end | 891 | `'4244-06-01T08:05:55.054876690884+00:00\n'`, `'8593-06-30T13:42:25+05:44\n'` |


## Leap seconds

- ERFA, through pyerfa 2.0.1.5, with its own leap second table. `dat` gets the UTC date and ERFA's own fraction of the day, from `dtf2d` and `jd2cal`, so a leap second gets 86400/86401, below 1.
- Timestamps known valid by the table, from 1972 on, given to ERFA: 22611. Different SI seconds since 1972 or TAI - UTC: 0. Before 1972, where TAI - UTC was not a whole number of seconds, not compared: 2949.
- SI seconds turned back into timestamps, of which 27 leap seconds, and given to ERFA for their SI seconds: 8665. Different: 0.

