# Cross-check with other parsers

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- This project: the `rfc3339` tool, as tested in TEST-RESULTS.md
- Go: `time.Parse(time.RFC3339Nano, s)`, go version go1.24.7 linux/amd64
- rfc3339-validator 0.1.4 (Python 3.13.17), called on the string as given. `jsonschema` calls it for its `date-time` check on the upper-cased string, so the lower case rows below do not apply to `jsonschema`.
- Seed: 20261025
- Strings: 182091
- Strings both this project and Go accept, read to a different instant: 0

Where each parser differs from this one, by the first category that fits the string:

| Parser | Differs by | Category | Strings | Example |
| --- | --- | --- | --- | --- |
| Go | rejects | lower case t or z | 19027 | `'1985-04-12t23:20:50.52z'`, `'2100-10-31t02:52:09+00:50'` |
| Go | rejects | second 60 | 3680 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| Go | accepts | offset hour above 23 or minute above 59 | 1970 | `'2000-01-01T00:00:00+24:00'`, `'2000-01-01T00:00:00+23:60'` |
| Go | accepts | a field with one digit | 435 | `'0099-09-29T8:05:14.9-13:23'`, `'6796-03-01T8:13:08+17:53'` |
| Go | accepts | comma before the fraction | 6 | `'2000-01-01T00:00:00,5Z'`, `'1900-01-02T22:19:55,9-00:00'` |
| rfc3339-validator | rejects | lower case t or z | 19027 | `'1985-04-12t23:20:50.52z'`, `'2100-10-31t02:52:09+00:50'` |
| rfc3339-validator | rejects | second 60 | 3680 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| rfc3339-validator | rejects | year 0000 | 1224 | `'0000-01-01T00:00:00Z'`, `'0000-01-01T12:00:00Z'` |
| rfc3339-validator | accepts | line break at the end | 855 | `'4244-06-01T08:05:55.054876690884+00:00\n'`, `'5263-10-30T07:22:33.52-07:24\n'` |


## Leap seconds

- ERFA, through pyerfa 2.0.1.5, with its own leap second table
- Timestamps known valid by the table, from 1972 on, given to ERFA: 19637. Different SI seconds since 1972 or TAI - UTC: 0. Before 1972, where TAI - UTC was not a whole number of seconds, not compared: 1965.
- SI seconds turned back into timestamps, of which 27 leap seconds, and given to ERFA for their SI seconds: 8666. Different: 0.


## RFC 9557

- Node v22.22.0, `Temporal.Instant.from`, with `--harmony-temporal`: V8's Temporal behind a flag, older than the current proposal
- Strings: 6992, of which this project reads 5193. The same answer, read or refused: 2737.

Where Temporal differs from this project, by the first category that fits the string:

| Temporal | Category | Strings | Example |
| --- | --- | --- | --- |
| refuses | a critical item, which Temporal refuses when it does not act on it | 2291 | `'2022-07-08T00:14:07+01:00[!Europe/Paris]'`, `'2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]'` |
| refuses | an experimental key | 676 | `'1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]'`, `'1972-02-01T13:53:54-10:37[_=X1][u-ca=hebrew]'` |
| refuses | an unknown elective key | 645 | `'2022-07-08T00:14:07+01:00[knort=blargel]'`, `'4960-06-30T10:33:21-04:31[knort=gregory]'` |
| refuses | a fraction of more than nine digits, finer than Temporal's nanoseconds | 418 | `'5720-01-31T23:59:60.26153083810657+00:00[Etc/GMT+5][!_=a-b][_foo=japanese]'`, `'2490-07-01t16:59:07.026416563048384470366623+04:19[a-b_c9=chinese]'` |
| refuses | a calendar Temporal does not know | 119 | `'3221-10-31T23:59:60+00:00[a.b-c+d_e][u-ca=blargel]'`, `'2022-07-08T00:14:07+00:00[u-ca=0]'` |
| refuses | a repeated elective `u-ca` | 64 | `'2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]'`, `'2024-02-04T15:17:00+23:59[+01:00][x=a-b][u-ca=a-b][u-ca=blargel]'` |
| refuses | a one-part time zone name | 32 | `'2404-02-29T00:37:44.236447+18:26[a.b-c+d_e]'`, `'3793-03-02T15:50:39.27-20:39[a.b-c+d_e]'` |
| refuses | another time zone name | 7 | `'2022-07-08T00:14:07Z[Etc/G.T+5]'`, `'9167-04-30T21:08:20.7+11:30[Etc/GMT+Z]'` |
| accepts | a `[` inside an item | 1 | `'1019-06-30T05:31:37+00:34[+23:59][u-ca=blargel[]'` |
| accepts | a time zone offset with no colon, as ISO 8601's basic format writes it | 1 | `'6121-04-02t21:22:26.9+05:04[+0530]'` |
| accepts | another suffix the grammar refuses | 1 | `'5984-06-01T02:30:25.893247-11:17[u-ca=gregory]]'` |
