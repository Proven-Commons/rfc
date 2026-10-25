# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, and the RFC 3339 rules copied into this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 98931 of the inputs are mutated timestamps
- By kind: compare 42725, error 18, grid 16998, mutated 98931, near miss 42347, valid 98981
- Strings parsed: 257257, of which 118758 accepted (6407 with a leap second) and 138499 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 110381
- Pairs ordered: 42725 (14309 before, 12000 same instant, 14324 after, 2092 with a string rejected)
- Malformed requests answered `error`: 18 of 18
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
