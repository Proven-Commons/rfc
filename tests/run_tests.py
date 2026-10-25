#!/usr/bin/env python3
"""Differential tests: the Lean parser against Python's date code.

There are two oracles:

- Python's `datetime` and `calendar` modules. `calendar.isleap` and
  `calendar.mdays` give the month lengths, `datetime` arithmetic applies
  offsets and counts seconds since the epoch, and
  `datetime.fromisoformat` reads every accepted timestamp it can
  represent (years 1 to 9999, seconds 0 to 59) and must agree on every
  field.
- A copy of the rules of RFC 3339, sections 5.6 and 5.7, written here
  from the RFC: a regular expression for the grammar, then the ranges,
  the month lengths and the leap second rule. It decides which strings
  are accepted, since `fromisoformat` also reads ISO 8601 forms that
  RFC 3339 does not allow.

Inputs come from a recorded seed:

- valid timestamps with random fields, weighted toward month ends,
  29 February, leap seconds, long fractions, and every offset form;
- near misses: one field just out of range;
- mutations of valid timestamps: a character replaced, deleted,
  inserted or swapped, the string cut short or extended, a digit
  replaced by a non-ASCII digit, a line break or NUL put in. A mutation
  that leaves the string unchanged is drawn again;
- every day from 0 to 32 of every month from 0 to 13 in years chosen
  for the leap year rule, and second 60 at every month end of three
  years under 15 offsets, at the one local minute that can be a leap
  second and at the minutes either side;
- pairs of timestamps to order, including pairs that name the same
  instant with different offsets or fractions;
- malformed requests, which the tool must answer with `error`.

For every input the Lean answer must equal the oracle's.

    python3 tests/run_tests.py [--seed N] [--count N]

It builds the executable first, writes tests/TEST-RESULTS.md, and exits
non-zero if any input disagrees.
"""

import argparse
import calendar
import itertools
import platform
import random
import re
import subprocess
import sys
import threading
from datetime import datetime, timedelta, timezone
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "rfc3339"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 1800
BUILD_TIMEOUT = 3600

# The grammar of RFC 3339, section 5.6, in ASCII digits only. `T` and `Z`
# may be lower case (the note under the grammar).
GRAMMAR = re.compile(
    r"([0-9]{4})-([0-9]{2})-([0-9]{2})[Tt]([0-9]{2}):([0-9]{2}):([0-9]{2})"
    r"(?:\.([0-9]+))?([Zz]|([+-])([0-9]{2}):([0-9]{2}))")

EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)
# The Gregorian calendar repeats every 400 years, which are 146097 days.
# Years 0, 1 and 9999, where `datetime` cannot hold the date or the UTC
# date a day away, are moved by 400 years for the arithmetic, and the
# seconds moved back.
CYCLE_DAYS = 146097


def month_length(year, month):
    if month == 2 and calendar.isleap(year):
        return 29
    return calendar.mdays[month]


def shifted(year):
    """A year `datetime` can hold with the same calendar, and the days
    the move adds."""
    if year < 2:
        return year + 400, CYCLE_DAYS
    if year > 9998:
        return year - 400, -CYCLE_DAYS
    return year, 0


def utc_parts(f):
    """The UTC date and time of the minute the timestamp falls in, and
    the whole seconds since the epoch, by `datetime` arithmetic."""
    year, days = shifted(f["year"])
    tz = timezone(timedelta(minutes=f["offset_minutes"]))
    local = datetime(year, f["month"], f["day"], f["hour"], f["minute"], tzinfo=tz)
    utc = local.astimezone(timezone.utc)
    delta = local - EPOCH
    seconds = (delta.days - days) * 86400 + delta.seconds + f["second"]
    return utc, seconds


def reference(s):
    """The RFC 3339 rules: the fields of `s`, or None when RFC 3339 does
    not allow it."""
    m = GRAMMAR.fullmatch(s)
    if not m:
        return None
    year, month, day, hour, minute, second = (int(m.group(i)) for i in range(1, 7))
    frac = m.group(7) or ""
    if m.group(8) in "Zz":
        off_text, off = "Z", 0
    else:
        oh, om = int(m.group(10)), int(m.group(11))
        if oh > 23 or om > 59:
            return None
        off_text = m.group(8)
        off = (oh * 60 + om) * (1 if m.group(9) == "+" else -1)
    if not (1 <= month <= 12 and 1 <= day <= month_length(year, month)):
        return None
    if hour > 23 or minute > 59 or second > 60:
        return None
    f = dict(year=year, month=month, day=day, hour=hour, minute=minute, second=second,
             fraction=frac, offset=off_text, offset_minutes=off)
    utc, seconds = utc_parts(f)
    if second == 60:
        # Section 5.7: at the end of a month, in UTC.
        if not (utc.hour == 23 and utc.minute == 59 and (utc + timedelta(days=1)).day == 1):
            return None
    f["unix"] = seconds
    f["print"] = s.upper()
    return f


def answer(f):
    if f is None:
        return "REJECT"
    return "\t".join(["OK", f["print"], str(f["unix"])] +
                     [str(f[k]) for k in ("year", "month", "day", "hour", "minute", "second")] +
                     [f["fraction"], f["offset"]])


def fromisoformat_agrees(f):
    """Whether `datetime.fromisoformat` reads the upper case form to the
    same fields, offset and instant. Only for what it can hold."""
    if f["year"] < 1 or f["second"] == 60:
        return None
    try:
        dt = datetime.fromisoformat(f["print"])
    except ValueError:
        return False
    micro = int((f["fraction"] + "000000")[:6])
    return ((dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, dt.microsecond) ==
            (f["year"], f["month"], f["day"], f["hour"], f["minute"], f["second"], micro) and
            dt.utcoffset() == timedelta(minutes=f["offset_minutes"]) and
            (dt.replace(microsecond=0) - EPOCH) == timedelta(seconds=f["unix"]))


def instant(f):
    return f["unix"] + Fraction(int(f["fraction"] or "0"), 10 ** len(f["fraction"]))


def order(a, b):
    fa, fb = reference(a), reference(b)
    if fa is None or fb is None:
        return "REJECT"
    x, y = instant(fa), instant(fb)
    return "<" if x < y else ">" if x > y else "="


# Generators.

def offset_text(minutes, rng, zulu_ok=True):
    if minutes == 0 and zulu_ok and rng.random() < 0.5:
        return rng.choice("Zz")
    sign = "-" if minutes < 0 or (minutes == 0 and rng.random() < 0.3) else "+"
    m = abs(minutes)
    return f"{sign}{m // 60:02d}:{m % 60:02d}"


def stamp(year, month, day, hour, minute, second, frac, off, t="T"):
    return (f"{year:04d}-{month:02d}-{day:02d}{t}{hour:02d}:{minute:02d}:{second:02d}"
            + (f".{frac}" if frac else "") + off)


def random_fraction(rng):
    r = rng.random()
    if r < 0.4:
        return ""
    n = rng.choice([1, 1, 2, 3, 3, 6, 6, 9, 12]) if r < 0.95 else rng.randint(13, 40)
    return "".join(rng.choice("0123456789") for _ in range(n))


def random_offset_minutes(rng):
    r = rng.random()
    if r < 0.3:
        return 0
    if r < 0.4:
        return rng.choice([-1439, 1439, -1, 1, -60, 60, 330, 345, -570, 840, -720, 720])
    return rng.randint(-1439, 1439)


def random_year(rng):
    if rng.random() < 0.2:
        return rng.choice([0, 1, 4, 99, 100, 400, 1900, 1970, 1972, 2000, 2024, 2100, 9998, 9999])
    return rng.randint(0, 9999)


def random_valid(rng):
    year, month = random_year(rng), rng.randint(1, 12)
    last = month_length(year, month)
    day = rng.choice([1, 2, last - 1, last, rng.randint(1, last)])
    hour, minute = rng.randint(0, 23), rng.randint(0, 59)
    off = random_offset_minutes(rng)
    second = rng.randint(0, 59)
    t = "T" if rng.random() < 0.85 else "t"
    if rng.random() < 0.05:
        # A leap second: 23:59 UTC on a month's last day, in local time.
        utc = datetime(shifted(year)[0], month, last, 23, 59) + timedelta(minutes=off)
        year = utc.year - (shifted(year)[0] - year)
        if not 0 <= year <= 9999:
            year, utc, off = 1990, datetime(1990, 12, 31, 23, 59), 0
        month, day, hour, minute, second = utc.month, utc.day, utc.hour, utc.minute, 60
    return stamp(year, month, day, hour, minute, second, random_fraction(rng),
                 offset_text(off, rng), t)


def near_miss(rng):
    year, month = random_year(rng), rng.randint(1, 12)
    day, hour, minute, second = rng.randint(1, 28), rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59)
    oh, om, sign = rng.randint(0, 23), rng.randint(0, 59), rng.choice("+-")
    which = rng.randrange(10)
    if which == 0:
        month = rng.choice([0, 13, 19, 99])
    elif which == 1:
        day = month_length(year, month) + rng.choice([1, 2, 69])
    elif which == 2:
        day = 0
    elif which == 3:
        hour = rng.choice([24, 25, 99])
    elif which == 4:
        minute = rng.choice([60, 99])
    elif which == 5:
        second = rng.choice([60, 61, 99])
    elif which == 6:
        oh = rng.choice([24, 99])
    elif which == 7:
        om = rng.choice([60, 99])
    elif which == 8:
        year, month, day = rng.choice([1900, 2100, 2001, 1999, 2200, 1800]), 2, 29
    else:
        second = 60
        day = month_length(year, month)
    off = f"{sign}{oh:02d}:{om:02d}" if rng.random() < 0.7 else "Z"
    return stamp(year, month, day, hour, minute, second, random_fraction(rng), off)


ODD_CHARS = ["0", "9", "-", ":", ".", "+", "T", "t", "Z", "z", " ", "_", "/", ",", "a", "Y",
             "\n", "\r", "\t", "\x00", "٠", "৪", "０", "\U0001d7d8", "é",
             "−", "‐", " ", "﻿"]


def mutate(rng, s):
    cs = list(s)
    op = rng.randrange(8)
    if op == 0 and cs:
        cs[rng.randrange(len(cs))] = rng.choice(ODD_CHARS)
    elif op == 1 and cs:
        del cs[rng.randrange(len(cs))]
    elif op == 2:
        cs.insert(rng.randint(0, len(cs)), rng.choice(ODD_CHARS))
    elif op == 3 and len(cs) > 1:
        i = rng.randrange(len(cs) - 1)
        cs[i], cs[i + 1] = cs[i + 1], cs[i]
    elif op == 4 and cs:
        cs = cs[: rng.randrange(len(cs))]
    elif op == 5:
        cs += list(rng.choice(["Z", "0", ".5", " ", "\n", "+00:00", "Zz"]))
    elif op == 6:
        digits = [i for i, c in enumerate(cs) if c.isdigit()]
        if digits:
            i = rng.choice(digits)
            cs[i] = chr(rng.choice([0x0660, 0x09E6, 0xFF10, 0x1D7CE]) + int(cs[i]))
    else:
        cs = list(s.swapcase() if rng.random() < 0.5 else s.replace("T", " ").replace("t", " "))
    return "".join(cs)


def day_grid():
    for year in [0, 1, 4, 100, 400, 1900, 1996, 2000, 2001, 2004, 2100, 2400, 9999]:
        for month in range(14):
            for day in range(33):
                yield stamp(year, month, day, 12, 0, 0, "", "Z")


def leap_grid():
    offsets = [-1439, -720, -481, -480, -60, -1, 0, 1, 60, 330, 345, 720, 1439]
    for year in [1990, 2000, 2001]:
        for month in range(1, 13):
            last = month_length(year, month)
            for day in sorted({1, 2, last - 1, last}):
                for off in offsets:
                    # The local minute that is 23:59 UTC on this date's day,
                    # and the minutes either side of it.
                    base = (23 * 60 + 59 + off) % 1440
                    for minute_of_day in {base, (base - 1) % 1440, (base + 1) % 1440}:
                        h, m = divmod(minute_of_day, 60)
                        for text in {f"+{off // 60:02d}:{off % 60:02d}" if off >= 0 else
                                     f"-{-off // 60:02d}:{-off % 60:02d}",
                                     *(["Z", "-00:00"] if off == 0 else [])}:
                            yield stamp(year, month, day, h, m, 60, "", text)


def same_instant_pair(rng):
    """Two spellings of one instant: different offsets, or a fraction
    with trailing zeros."""
    year, month = rng.randint(1, 9998), rng.randint(1, 12)
    day = rng.randint(1, month_length(year, month))
    base = datetime(year, month, day, rng.randint(0, 23), rng.randint(0, 59), rng.randint(0, 59))
    frac = random_fraction(rng)
    o1, o2 = random_offset_minutes(rng), random_offset_minutes(rng)
    l1, l2 = base + timedelta(minutes=o1), base + timedelta(minutes=o2)
    f2 = frac + "0" * rng.randint(0, 3) if frac else rng.choice(["", "0", "000"])
    if rng.random() < 0.3:
        # Nudge the second fraction by one unit in its last place.
        f2 = (frac or "0") + "1"
    a = stamp(l1.year, l1.month, l1.day, l1.hour, l1.minute, l1.second, frac, offset_text(o1, rng))
    b = stamp(l2.year, l2.month, l2.day, l2.hour, l2.minute, l2.second, f2, offset_text(o2, rng))
    return (a, b) if rng.random() < 0.5 else (b, a)


MALFORMED = [
    ("frob 30", "unknown operation"),
    ("PARSE 30", "operations are lower case"),
    ("parse", "no argument"),
    ("parse 3", "an odd number of hex digits"),
    ("parse 3G", "not a hex digit"),
    ("parse 3A", "hex digits are lower case"),
    ("parse ff", "not UTF-8"),
    ("parse c0af", "an overlong encoding, not UTF-8"),
    ("parse eda080", "a surrogate, not UTF-8"),
    ("parse 30 30", "two arguments to parse"),
    ("compare 30", "one argument to compare"),
    ("compare 30 30 30", "three arguments to compare"),
    (" parse 30", "a leading space"),
    ("parse  30", "two spaces"),
]

# A last line with no LF must still be answered.
AT_EOF = [
    ("parse " + "1985-04-12T23:20:50.52Z".encode().hex(), None),
    ("compare " + "1990-12-31T23:59:60Z".encode().hex() + " " +
     "1991-01-01T00:00:00Z".encode().hex(), "="),
]


def hexed(s):
    return s.encode("utf-8").hex()


def cases(seed, count):
    """(label, request, expected answer, mutated) for each input."""
    rng = random.Random(seed)
    fixed = []
    for s in itertools.chain(day_grid(), leap_grid()):
        fixed.append(("grid", f"parse {hexed(s)}", answer(reference(s)), False))
    for req, _ in MALFORMED:
        fixed.append(("error", req, "error", False))
    made = 0
    for item in fixed[:count]:
        yield item
        made += 1
    while made < count:
        r = rng.random()
        if r < 0.35:
            s, label, mutated = random_valid(rng), "valid", False
        elif r < 0.5:
            s, label, mutated = near_miss(rng), "near miss", False
        elif r < 0.85:
            base = random_valid(rng)
            s = mutate(rng, base)
            while s == base:
                s = mutate(rng, base)
            label, mutated = "mutated", True
        else:
            if rng.random() < 0.5:
                a, b = same_instant_pair(rng)
            else:
                a, b = random_valid(rng), random_valid(rng)
            yield ("compare", f"compare {hexed(a)} {hexed(b)}", order(a, b), False)
            made += 1
            continue
        yield (label, f"parse {hexed(s)}", answer(reference(s)), mutated)
        made += 1


def run_tool(data, timeout=TIMEOUT):
    """The tool's answer lines for `data`, and a note on how the run
    failed, or None. No right answer is longer than its request plus 64
    bytes, so a tool that writes more than that is stopped."""
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (data.count("\n") + 1)
    try:
        proc = subprocess.Popen([str(EXE), "serve"], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as e:
        return [], f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out, limit)),
               threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines, problem


def oracle():
    return (f"Python {platform.python_version()} `datetime` and `calendar`, and the "
            f"RFC 3339 rules copied into this script")


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=count, default=300_000)
    args = ap.parse_args()
    if sys.version_info < (3, 11):
        sys.exit("needs Python 3.11 or later, for datetime.fromisoformat with offsets and Z")

    # Always build, so the tests never run an executable older than the code.
    try:
        build = subprocess.run(["lake", "build", "rfc3339"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        built, log = build.returncode == 0, build.stdout + build.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        built, log = False, str(e)
    if not built:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0", "- Failures: 1 (`lake build rfc3339` failed)", ""])
        sys.exit("lake build rfc3339 failed:\n" + log)

    items = list(cases(args.seed, args.count))
    out, problem = run_tool("".join(req + "\n" for _, req, _, _ in items))
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))

    # The second oracle: every accepted timestamp that `datetime` can
    # hold must read the same there.
    checked = 0
    for label, req, want, _ in items:
        if req.startswith("parse ") and want.startswith("OK"):
            s = bytes.fromhex(req.split(" ")[1]).decode("utf-8")
            agrees = fromisoformat_agrees(reference(s))
            if agrees is None:
                continue
            checked += 1
            if not agrees:
                failures.append((req, "datetime.fromisoformat to agree", s))

    eof_right = 0
    for req, want in AT_EOF:
        if want is None:
            s = bytes.fromhex(req.split(" ")[1]).decode("utf-8")
            want = answer(reference(s))
        got, problem = run_tool(req, timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    by_label = {}
    for label, _, _, _ in items:
        by_label[label] = by_label.get(label, 0) + 1
    parsed = [want for label, req, want, _ in items if label != "error" and req.startswith("parse ")]
    accepted = sum(1 for w in parsed if w.startswith("OK"))
    leap = sum(1 for w in parsed if w.startswith("OK") and w.split("\t")[8] == "60")
    orders = [want for label, _, want, _ in items if label == "compare"]
    mutated = sum(1 for item in items if item[3])
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        f"- Mutated: {mutated} of the inputs are mutated timestamps",
        f"- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Strings parsed: {len(parsed)}, of which {accepted} accepted "
        f"({leap} with a leap second) and {len(parsed) - accepted} rejected",
        f"- Accepted strings also read by `datetime.fromisoformat`, with the same fields, "
        f"offset and seconds: {checked}",
        f"- Pairs ordered: {len(orders)} ({orders.count('<')} before, {orders.count('=')} same "
        f"instant, {orders.count('>')} after, {orders.count('REJECT')} with a string rejected)",
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Last lines with no LF, sent alone, answered right: {eof_right} of {len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:160]!r}`: expected `{want[:120]!r}`, got `{got[:120]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    agree = sum(1 for item, got in zip(items, out) if got == item[2])
    print(f"{agree}/{len(items)} inputs agree, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
