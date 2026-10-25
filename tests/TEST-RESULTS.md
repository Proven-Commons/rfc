# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, and the RFC 3339 rules copied into this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 100570 of the inputs are mutated timestamps
- By kind: compare 43243, error 14, grid 12486, mutated 100570, near miss 43080, valid 100607
- Strings parsed: 256743, of which 120119 accepted (6123 with a leap second) and 136624 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 112060
- Pairs ordered: 43243 (14462 before, 12196 same instant, 14572 after, 2013 with a string rejected)
- Malformed requests answered `error`: 14 of 14
- Requests ending in CR LF: every seventh, 42857
- Strings also given to `rfc3339 check` as arguments, in batches of 500: 20000, and once with no arguments
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
