# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, the RFC 3339 rules copied into this script, for leap seconds tzdata's `/usr/share/zoneinfo/leap-seconds.list`, read by this script, and for RFC 9557 its grammar and rules written in this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 67589 of the inputs are mutated timestamps
- By kind: compare 29508, error 48, fromsi 9393, fromunix 44578, grid 16998, ixdtf 7143, known 27493, mutated 67589, near miss 29155, valid 68095
- Strings parsed: 181837, of which 83546 accepted (4617 with a leap second) and 98291 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 77425
- Pairs ordered: 29508 (9918 before, 8280 same instant, 9846 after, 1464 with a string rejected)
- Unix seconds turned back into timestamps: 44578, of which 671 outside years 0000 to 9999
- Leap second table: /usr/share/zoneinfo/leap-seconds.list, 28 lines, 27 leap seconds, expires 2027-06-28, last updated at NTP time 3992312697, hash line `a9bad145 84c31c70 758402aa b37bfd54 5923836a`
- Timestamps checked against the table (`known`): 27493, of which 224 leap seconds of the table, 5700 with a second 60 it does not list, and 1242 rejected
- SI seconds turned back into timestamps (`fromsi`): 9393, of which 27 leap seconds and 698 outside 1972 to 9999
- RFC 9557 strings (`ixdtf`): 7143, of which 5302 read, 3122 of them erroneous for the example application, and 1841 refused
- Malformed requests answered `error`: 48 of 48
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
