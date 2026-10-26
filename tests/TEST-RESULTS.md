# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, the RFC 3339 rules copied into this script, for leap seconds tzdata's `/usr/share/zoneinfo/leap-seconds.list`, read by this script, and for RFC 9557 its grammar and rules written in this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 67687 of the inputs are mutated timestamps
- By kind: compare 29458, error 39, fromsi 9356, fromunix 44579, grid 16998, ixdtf 6992, known 27497, mutated 67687, near miss 29289, valid 68105
- Strings parsed: 182079, of which 83586 accepted (4568 with a leap second) and 98493 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 77505
- Pairs ordered: 29458 (9861 before, 8209 same instant, 9923 after, 1465 with a string rejected)
- Unix seconds turned back into timestamps: 44579, of which 657 outside years 0000 to 9999
- Leap second table: /usr/share/zoneinfo/leap-seconds.list, 28 lines, 27 leap seconds, expires 2027-06-28
- Timestamps checked against the table (`known`): 27497, of which 236 leap seconds of the table, 5895 with a second 60 it does not list, and 0 rejected
- SI seconds turned back into timestamps (`fromsi`): 9356, of which 27 leap seconds and 690 outside 1972 to 9999
- RFC 9557 strings (`ixdtf`): 6992, of which 5193 read, 3083 of them erroneous for the example application, and 1799 refused
- Malformed requests answered `error`: 39 of 39
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
