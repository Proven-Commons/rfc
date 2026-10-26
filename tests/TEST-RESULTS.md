# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, and the RFC 3339 rules copied into this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 79241 of the inputs are mutated timestamps
- By kind: compare 34149, error 27, fromunix 56056, grid 16998, mutated 79241, near miss 33926, valid 79603
- Strings parsed: 209768, of which 96503 accepted (5227 with a leap second) and 113265 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 89586
- Pairs ordered: 34149 (11557 before, 9582 same instant, 11345 after, 1665 with a string rejected)
- Unix seconds turned back into timestamps: 56056, of which 1278 outside years 0000 to 9999
- Malformed requests answered `error`: 27 of 27
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
