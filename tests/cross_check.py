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
instants must match to the nanosecond.

For the leap second table, the timestamps tests/run_tests.py sends as
`known` requests, and the SI seconds it sends as `fromsi`, go to ERFA,
a BSD-licensed C library derived from the IAU's SOFA, through pyerfa, which keeps its
own leap second table: `dat` gives TAI - UTC, given the UTC date and
ERFA's own fraction of the day, and `dtf2d` with `utctai` the TAI time,
from which the SI seconds since 1972-01-01T00:00:00Z follow. It needs
pyerfa:

    pip install --target .lake/oracle-packages pyerfa==2.0.1.5

For RFC 9557, the strings tests/run_tests.py sends as `ixdtf` requests go
to `Temporal.Instant.from` in Node, with `--harmony-temporal`. That is
V8's own Temporal behind a flag, an older one than the current proposal:
it refuses some strings the proposal now reads. Each difference is put in
the first category below that fits it. The report records the flag,
Node's version, and the versions of V8, ICU and the time zone data that
Node gives in `process.versions`, so that the run can be repeated.

The counts go to tests/CROSS-CHECK.md.
"""

import argparse
import json
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


def erfa_elapsed(erfa, y, mo, d, h, mi, sec, base):
    """SI seconds from `base`, a TAI two-part Julian date, to the UTC time,
    by ERFA."""
    u1, u2 = erfa.dtf2d("UTC", y, mo, d, h, mi, float(sec))
    t1, t2 = erfa.utctai(u1, u2)
    return round(((t1 - base[0]) + (t2 - base[1])) * 86400)


def leap_section(args):
    sys.path.insert(0, str(ROOT / ".lake" / "oracle-packages"))
    try:
        import erfa
    except ImportError:
        sys.exit("needs pyerfa: pip install --target .lake/oracle-packages pyerfa==2.0.1.5")
    import warnings
    from importlib.metadata import version
    # ERFA warns of a "dubious year" after its table's last entry; its
    # answers still assume no later leap second, as the table here does.
    warnings.simplefilter("ignore")
    items = list(run_tests.cases(args.seed, args.count))
    knowns = [bytes.fromhex(req.split(" ")[1]).decode("utf-8") for label, req, _, _ in items
              if label == "known"]
    sis = [int(req.split(" ")[1]) for label, req, _, _ in items if label == "fromsi"]
    ours_k, problem = run_tests.run_tool("".join(f"known {run_tests.hexed(k)}\n" for k in knowns))
    if problem or len(ours_k) != len(knowns):
        sys.exit(f"the tool failed: {problem}")
    ours_s, problem = run_tests.run_tool("".join(f"fromsi {n}\n" for n in sis))
    if problem or len(ours_s) != len(sis):
        sys.exit(f"the tool failed: {problem}")
    b1, b2 = erfa.dtf2d("UTC", 1972, 1, 1, 0, 0, 0.0)
    base = erfa.utctai(b1, b2)
    k_checked, k_before, k_diff = 0, 0, []
    for s, ours in zip(knowns, ours_k):
        if not ours.startswith("OK"):
            continue
        _, si, tai = ours.split("\t")
        if tai == "-":
            k_before += 1
            continue
        f = run_tests.reference(s)
        utc, _ = run_tests.utc_parts(f)
        # utc_parts moves years `datetime` cannot hold by 400 years; move
        # the UTC year back.
        year = utc.year + f["year"] - run_tests.shifted(f["year"])[0]
        # ERFA's own fraction of the day. Its UTC day that ends in a leap
        # second has 86401 seconds, so the leap second gets 86400/86401.
        # That keeps it below 1, in the range 0 to 1 that eraDat documents.
        # From 1972 on, eraDat reads only the date (its Note 4).
        _, _, _, fd = erfa.jd2cal(*erfa.dtf2d("UTC", year, utc.month, utc.day, utc.hour,
                                               utc.minute, float(f["second"])))
        theirs_tai = erfa.dat(year, utc.month, utc.day, fd)
        theirs_si = erfa_elapsed(erfa, year, utc.month, utc.day, utc.hour, utc.minute,
                                 f["second"], base)
        k_checked += 1
        if (int(si), int(tai)) != (theirs_si, round(theirs_tai)):
            k_diff.append((s, ours, f"{theirs_si}\t{theirs_tai}"))
    s_checked, s_leaps, s_diff = 0, 0, []
    for n, ours in zip(sis, ours_s):
        if ours == "NONE":
            continue
        m = re.fullmatch(r"([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})Z", ours)
        y, mo, d, h, mi, sec = map(int, m.groups())
        s_checked += 1
        s_leaps += sec == 60
        theirs = erfa_elapsed(erfa, y, mo, d, h, mi, sec, base)
        if theirs != n:
            s_diff.append((n, ours, theirs))
    lines = [
        "",
        "## Leap seconds",
        "",
        f"- ERFA, through pyerfa {version('pyerfa')}, with its own leap second table. `dat` "
        "gets the UTC date and ERFA's own fraction of the day, from `dtf2d` and `jd2cal`, "
        "so a leap second gets 86400/86401, below 1.",
        f"- Timestamps known valid by the table, from 1972 on, given to ERFA: {k_checked}. "
        f"Different SI seconds since 1972 or TAI - UTC: {len(k_diff)}. Before 1972, where "
        f"TAI - UTC was not a whole number of seconds, not compared: {k_before}.",
        f"- SI seconds turned back into timestamps, of which {s_leaps} leap seconds, and given "
        f"to ERFA for their SI seconds: {s_checked}. Different: {len(s_diff)}.",
        "",
    ]
    lines += [f"- `{s}`: this project `{o}`, ERFA `{t}`" for s, o, t in k_diff[:10]]
    lines += [f"- `fromsi {n}`: this project `{o}`, ERFA's SI seconds `{t}`" for n, o, t in s_diff[:10]]
    return lines


def ix_category(s, ours_ok):
    """Why Temporal reads `s` differently: the first reason that fits."""
    r = run_tests.ix_reference(s)
    if ours_ok:
        f, _, zone, tags = r
        if len(f["fraction"]) > 9:
            return "a fraction of more than nine digits, finer than Temporal's nanoseconds"
        if (zone and zone[0]) or any(c for c, _, _ in tags):
            return "a critical flag, which this Temporal refuses on any item"
        if any(k.startswith("_") for _, k, _ in tags):
            return "an experimental key"
        if len([k for _, k, _ in tags if k == "u-ca"]) > 1:
            return "a repeated elective `u-ca`"
        if any(k != "u-ca" for _, k, _ in tags):
            return "an unknown elective key"
        if tags and any(not 3 <= len(p) <= 8 for p in tags[0][2]):
            return "a calendar with a part outside 3 to 8 characters, which the older proposal refuses"
        if zone and zone[1][0] == "name":
            parts = zone[1][1].split("/")
            etc_gmt = re.fullmatch(r"Etc/GMT[+-](?:[0-9]|1[0-4])", zone[1][1])
            if not etc_gmt and any(re.search(r"[0-9+]", q) or len(q) > 14 for q in parts):
                return ("a time zone name with a digit or `+`, or a part over 14 characters, "
                        "which the older proposal refuses")
            return "another time zone name"
        return "other"
    i = s.find("[")
    if run_tests.reference(s if i < 0 else s[:i]) is None:
        return "an RFC 3339 part the RFC does not allow"
    if re.search(r"\[!?[+-][0-9]{4}\]", s):
        return "a time zone offset with no colon, as ISO 8601's basic format writes it"
    if re.search(r"\[[^\]]*\[", s):
        return "a `[` inside an item"
    return "another suffix the grammar refuses"


def ixdtf_section(args):
    import os
    strings = [bytes.fromhex(req.split(" ")[1]).decode("utf-8")
               for label, req, _, _ in run_tests.cases(args.seed, args.count) if label == "ixdtf"]
    ours, problem = run_tests.run_tool("".join(f"ixdtf {run_tests.hexed(x)}\n" for x in strings))
    if problem or len(ours) != len(strings):
        sys.exit(f"the tool failed: {problem}")
    flag = "--harmony-temporal"
    out = subprocess.run(["node", flag, str(GO_DIR / "ixdtf.js")],
                         input="".join(run_tests.hexed(x) + "\n" for x in strings),
                         capture_output=True, text=True, check=True)
    theirs = out.stdout.split("\n")[: len(strings)]
    node = subprocess.run(["node", "--version"], capture_output=True, text=True).stdout.strip()
    versions = json.loads(subprocess.run(["node", "-p", "JSON.stringify(process.versions)"],
                                         capture_output=True, text=True, check=True).stdout)
    tallies, examples = {}, {}
    for x, o, t in zip(strings, ours, theirs):
        ok, tok = o.startswith("OK"), t == "OK"
        if ok == tok:
            continue
        key = ("accepts" if tok else "refuses", ix_category(x, ok))
        tallies[key] = tallies.get(key, 0) + 1
        examples.setdefault(key, [])
        if len(examples[key]) < 2:
            examples[key].append(x)
    same = sum(1 for o, t in zip(ours, theirs) if o.startswith("OK") == (t == "OK"))
    lines = [
        "",
        "## RFC 9557",
        "",
        f"- Node {node}, `Temporal.Instant.from`, with `{flag}`: V8's Temporal behind a "
        "flag, older than the current proposal",
        f"- This Temporal is V8's own, here V8 {versions['v8']}. Node's `process.versions` also "
        f"gives ICU {versions['icu']} and time zone data {versions['tz']}.",
        f"- Strings: {len(strings)}, of which this project reads "
        f"{sum(1 for o in ours if o.startswith('OK'))}. The same answer, read or refused: {same}.",
        "",
        "Where Temporal differs from this project, by the first category that fits the string:",
        "",
        "| Temporal | Category | Strings | Example |",
        "| --- | --- | --- | --- |",
    ]
    for (how, cat), n in sorted(tallies.items(), key=lambda kv: (-kv[1], kv[0])):
        ex = ", ".join(f"`{e!r}`" for e in examples[(how, cat)])
        lines.append(f"| {how} | {cat} | {n} | {ex} |")
    return lines


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
    lines += leap_section(args)
    lines += ixdtf_section(args)
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(strings)} strings; report in {REPORT}")


if __name__ == "__main__":
    main()
