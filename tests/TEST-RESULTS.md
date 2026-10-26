# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, the RFC 3339 rules copied into this script, and for leap seconds tzdata's `/usr/share/zoneinfo/leap-seconds.list`, read by this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 67878 of the inputs are mutated timestamps
- By kind: compare 29413, error 44, fromsi 9360, fromunix 44543, grid 16998, known 34497, mutated 67878, near miss 29254, valid 68013
- Strings parsed: 182143, of which 83519 accepted (4666 with a leap second) and 98624 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 77331
- Pairs ordered: 29413 (9874 before, 8322 same instant, 9754 after, 1463 with a string rejected)
- Unix seconds turned back into timestamps: 44543, of which 679 outside years 0000 to 9999
- Leap second table: /usr/share/zoneinfo/leap-seconds.list, 28 lines, 27 leap seconds, expires 2027-06-28, last updated at NTP time 3992312697, hash line `a9bad145 84c31c70 758402aa b37bfd54 5923836a`
- Timestamps checked against the table (`known`): 34497, of which 267 leap seconds of the table, 6367 with a second 60 it does not list, and 2570 rejected
- SI seconds turned back into timestamps (`fromsi`): 9360, of which 27 leap seconds and 695 outside 1972 to 9999
- Malformed requests answered `error`: 44 of 44
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
