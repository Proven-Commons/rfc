#!/usr/bin/env python3
"""A one-off comparison of this parser with two widely used ones.

Unlike tests/run_tests.py, this is not part of the verified bar and is
not run in CI. It records where other parsers read RFC 3339 differently,
which is the reason the RFC's rules are proved here. It needs Go, and
the `rfc3339-validator` package, which `jsonschema` calls on the
upper-cased string to check the `date-time` format:

    pip install rfc3339-validator==0.1.4
    python3 tests/cross_check.py [--seed N] [--count N]

The strings are the ones tests/run_tests.py parses, from the same seed,
plus a few written out below. Each is given to this project's tool, to
Go's `time.Parse` with the `time.RFC3339Nano` layout, and to
`rfc3339_validator.validate_rfc3339`. Where a parser accepts what this
one rejects, or the reverse, the string is put in the first category
below that fits it. Where Go and this tool both accept a string, the
instants must match to the nanosecond. The counts go to
tests/CROSS-CHECK.md.
"""

import argparse
import platform
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_tests  # noqa: E402

ROOT = run_tests.ROOT
REPORT = ROOT / "tests" / "CROSS-CHECK.md"
GO_DIR = ROOT / "tests" / "cross_check"

PROBES = [
    "1985-04-12T23:20:50.52Z",
    "1985-04-12t23:20:50.52z",
    "1990-12-31T23:59:60Z",
    "1990-12-31T15:59:60-08:00",
    "0000-01-01T00:00:00Z",
    "2000-01-01T00:00:00+24:00",
    "2000-01-01T00:00:00+23:60",
    "2000-01-01T00:00:00,5Z",
    "2000-01-01T00:00:00.1234567891Z",
    "2000-02-30T00:00:00Z",
    "2000-01-01 00:00:00Z",
]

FIELDS = re.compile(r"([0-9]{4})-[0-9]{2}-[0-9]{2}.[0-9]{2}:[0-9]{2}:([0-9]{2})")


def category(s, ours_ok):
    """The first reason that fits why another parser reads `s`
    differently. `ours_ok` is whether the RFC's rules allow `s`."""
    m = FIELDS.match(s)
    if ours_ok:
        # The other parser rejects what the RFC allows.
        if any(c in s for c in "tz"):
            return "lower case t or z"
        if m and m.group(2) == "60":
            return "second 60"
        if m and m.group(1) == "0000":
            return "year 0000"
        return "other"
    # The other parser accepts what the RFC does not allow.
    if s.endswith("\n"):
        return "line break at the end"
    if re.search(r"[+-](2[4-9]|[3-9][0-9]):[0-9]{2}$|[+-][0-9]{2}:([6-9][0-9])$", s):
        return "offset hour above 23 or minute above 59"
    if re.search(r"[0-9],[0-9]", s):
        return "comma before the fraction"
    if re.fullmatch(r"[0-9]{4}-[0-9]{1,2}-[0-9]{1,2}[Tt][0-9]{1,2}:[0-9]{1,2}:[0-9]{1,2}.*", s) and not m:
        return "a field with one digit"
    if m and m.group(2) == "60":
        return "second 60 outside the last minute of a month in UTC"
    return "other"


def go_tool(strings):
    exe = ROOT / ".lake" / "cross_check_go"
    subprocess.run(["go", "build", "-o", str(exe), "main.go"], cwd=GO_DIR, check=True,
                   env={**__import__("os").environ, "GO111MODULE": "off"})
    data = "".join(s.encode("utf-8").hex() + "\n" for s in strings)
    out = subprocess.run([str(exe)], input=data, capture_output=True, text=True, check=True)
    return out.stdout.split("\n")[: len(strings)]


def go_version():
    out = subprocess.run(["go", "version"], capture_output=True, text=True)
    return out.stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=int, default=300_000)
    args = ap.parse_args()
    try:
        from rfc3339_validator import validate_rfc3339
    except ImportError:
        sys.exit("needs the rfc3339-validator package: pip install rfc3339-validator==0.1.4")
    from importlib.metadata import version

    strings = list(PROBES)
    for _, req, _, _ in run_tests.cases(args.seed, args.count):
        if req.startswith("parse ") and len(req.split(" ")) == 2:
            try:
                strings.append(bytes.fromhex(req.split(" ")[1]).decode("utf-8"))
            except ValueError:
                pass
    lean, problem = run_tests.run_tool("".join(f"parse {run_tests.hexed(s)}\n" for s in strings))
    if problem or len(lean) != len(strings):
        sys.exit(f"the tool failed: {problem}")
    go = go_tool(strings)

    tallies = {"Go": {}, "rfc3339-validator": {}}
    examples = {"Go": {}, "rfc3339-validator": {}}
    value_mismatch = []
    for s, ours, theirs in zip(strings, lean, go):
        ok = ours.startswith("OK")
        for name, other_ok in (("Go", theirs.startswith("OK")), ("rfc3339-validator", validate_rfc3339(s))):
            if other_ok == ok:
                continue
            key = ("accepts" if other_ok else "rejects", category(s, ok))
            tallies[name][key] = tallies[name].get(key, 0) + 1
            examples[name].setdefault(key, [])
            if len(examples[name][key]) < 3:
                examples[name][key].append(s)
        if ok and theirs.startswith("OK"):
            _, secs, nanos = theirs.split("\t")
            f = ours.split("\t")
            frac = (f[9] + "0" * 9)[:9]
            if (int(secs), int(nanos)) != (int(f[2]), int(frac)):
                value_mismatch.append((s, theirs, ours))

    lines = [
        "# Cross-check with other parsers",
        "",
        "Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.",
        "",
        f"- This project: the `rfc3339` tool, as tested in TEST-RESULTS.md",
        f"- Go: `time.Parse(time.RFC3339Nano, s)`, {go_version()}",
        f"- rfc3339-validator {version('rfc3339-validator')} (Python {platform.python_version()}), "
        "called on the string as given. `jsonschema` calls it for its `date-time` check on the "
        "upper-cased string, so the lower case rows below do not apply to `jsonschema`.",
        f"- Seed: {args.seed}",
        f"- Strings: {len(strings)}",
        f"- Strings both this project and Go accept, read to a different instant: {len(value_mismatch)}",
        "",
        "Where each parser differs from this one, by the first category that fits the string:",
        "",
        "| Parser | Differs by | Category | Strings | Example |",
        "| --- | --- | --- | --- | --- |",
    ]
    for name in tallies:
        for (how, cat), n in sorted(tallies[name].items(), key=lambda kv: (-kv[1], kv[0])):
            ex = ", ".join(f"`{e!r}`" for e in examples[name][(how, cat)][:2])
            lines.append(f"| {name} | {how} | {cat} | {n} | {ex} |")
    lines.append("")
    for s, theirs, ours in value_mismatch[:20]:
        lines.append(f"- Different instant: `{s!r}`: Go `{theirs}`, this project `{ours}`")
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(strings)} strings; report in {REPORT}")


if __name__ == "__main__":
    main()
