# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `datetime` and `calendar`, and the RFC 3339 rules copied into this script
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 300000
- Mutated: 100418 of the inputs are mutated timestamps
- By kind: compare 43101, error 14, grid 12486, mutated 100418, near miss 42805, valid 101176
- Strings parsed: 256885, of which 120527 accepted (6028 with a leap second) and 136358 rejected
- Accepted strings also read by `datetime.fromisoformat`, with the same fields, offset and seconds: 112584
- Pairs ordered: 43101 (13945 before, 15018 same instant, 14138 after, 0 with a string rejected)
- Malformed requests answered `error`: 14 of 14
- Last lines with no LF, sent alone, answered right: 2 of 2
- Failures: 0
