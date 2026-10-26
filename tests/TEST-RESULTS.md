# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, the RFC 3339 rules copied into this script, and for leap seconds tzdata's `/usr/share/zoneinfo/leap-seconds.list`, read by this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 67969 of the inputs are mutated timestamps
- By kind: compare 29344, error 35, fromsi 9381, fromunix 44688, grid 16998, known 34402, mutated 67969, near miss 29160, valid 68023
- Strings parsed: 182150, of which 83488 accepted (4661 with a leap second) and 98662 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 77297
- Pairs ordered: 29344 (9831 before, 8253 same instant, 9780 after, 1480 with a string rejected)
- Unix seconds turned back into timestamps: 44688, of which 704 outside years 0000 to 9999
- Leap second table: /usr/share/zoneinfo/leap-seconds.list, 28 lines, 27 leap seconds, expires 2027-06-28
- Timestamps checked against the table (`known`): 34402, of which 303 leap seconds of the table, 6821 with a second 60 it does not list, and 0 rejected
- SI seconds turned back into timestamps (`fromsi`): 9381, of which 27 leap seconds and 681 outside 1972 to 9999
- Malformed requests answered `error`: 35 of 35
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
