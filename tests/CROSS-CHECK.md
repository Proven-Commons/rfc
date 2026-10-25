# Cross-check with other parsers

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- This project: the `rfc3339` tool, as tested in TEST-RESULTS.md
- Go: `time.Parse(time.RFC3339Nano, s)`, go version go1.24.7 linux/amd64
- rfc3339-validator 0.1.4 (Python 3.13.17), called on the string as given. `jsonschema` calls it for its `date-time` check on the upper-cased string, so the lower case rows below do not apply to `jsonschema`.
- Seed: 20261025
- Strings: 256755
- Strings both this project and Go accept, read to a different instant: 0

Where each parser differs from this one, by the first category that fits the string:

| Parser | Differs by | Category | Strings | Example |
| --- | --- | --- | --- | --- |
| Go | rejects | lower case t or z | 28347 | `'1985-04-12t23:20:50.52z'`, `'3864-12-02t01:14:12.577732z'` |
| Go | rejects | second 60 | 4691 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| Go | accepts | offset hour above 23 or minute above 59 | 3033 | `'2000-01-01T00:00:00+24:00'`, `'2000-01-01T00:00:00+23:60'` |
| Go | accepts | a field with one digit | 702 | `'5585-08-01T5:46:19.534-17:35'`, `'2098-08-07T1:15:55-19:39'` |
| Go | accepts | comma before the fraction | 5 | `'2000-01-01T00:00:00,5Z'`, `'3237-07-31T04:42:37,135148-08:01'` |
| rfc3339-validator | rejects | lower case t or z | 28347 | `'1985-04-12t23:20:50.52z'`, `'3864-12-02t01:14:12.577732z'` |
| rfc3339-validator | rejects | second 60 | 4691 | `'1990-12-31T23:59:60Z'`, `'1990-12-31T15:59:60-08:00'` |
| rfc3339-validator | rejects | year 0000 | 1583 | `'0000-01-01T00:00:00Z'`, `'0000-01-01T12:00:00Z'` |
| rfc3339-validator | accepts | line break at the end | 1330 | `'2513-04-29T17:09:04.19696594243724-20:08\n'`, `'8984-09-01T04:21:23+15:45\n'` |

