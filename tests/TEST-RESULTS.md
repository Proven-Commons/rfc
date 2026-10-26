# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, the RFC 3339 rules copied into this script, for leap seconds tzdata's `/usr/share/zoneinfo/leap-seconds.list`, read by this script, and for RFC 9557 its grammar and rules written in this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 67662 of the inputs are mutated timestamps
- By kind: compare 29524, error 48, fromsi 9358, fromunix 44565, grid 16998, ixdtf 7157, known 27468, mutated 67662, near miss 29208, valid 68012
- Strings parsed: 181880, of which 83519 accepted (4589 with a leap second) and 98361 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 77424
- Pairs ordered: 29524 (9906 before, 8293 same instant, 9859 after, 1466 with a string rejected)
- Unix seconds turned back into timestamps: 44565, of which 648 outside years 0000 to 9999
- Leap second table: /usr/share/zoneinfo/leap-seconds.list, 28 lines, 27 leap seconds, expires 2027-06-28, last updated at NTP time 3992312697, hash line `a9bad145 84c31c70 758402aa b37bfd54 5923836a`
- Timestamps checked against the table (`known`): 27468, of which 224 leap seconds of the table, 5703 with a second 60 it does not list, and 1230 rejected
- SI seconds turned back into timestamps (`fromsi`): 9358, of which 27 leap seconds and 702 outside 1972 to 9999
- RFC 9557 strings (`ixdtf`): 7157, of which 5299 read, 3126 of them erroneous for the example application, and 1858 refused
- Malformed requests answered `error`: 48 of 48
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
