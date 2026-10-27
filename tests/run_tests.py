#!/usr/bin/env python3
"""Differential tests: the Lean parser against Python's date code.

For RFC 3339 itself there are two oracles:

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
  for the leap year rule, and second 60 at every month end of five
  years, 0000 and 9999 among them, under 15 offsets, at the one local
  minute that can be a leap second and at the minutes either side;
- 0000-01-01 and 9999-12-31 under offsets that move the UTC date out
  of years 0000 to 9999, near both ends of the day, with seconds 0, 59
  and 60, each parsed and each compared with the next;
- pairs of timestamps to order, including pairs that name the same
  instant with different offsets or fractions, leap seconds next to
  the seconds around them, and pairs with a string that is rejected;
- Unix seconds to turn back into timestamps: the ends of the range and
  one second past each, the first second of every month of years
  chosen for the leap year rule and of every year from 0000 to 9999,
  with the seconds either side, random
  seconds in and around the range, and the seconds of valid timestamps.
  `datetime` arithmetic gives the expected UTC timestamp, with year 0
  moved by 400 years as above;
- for the leap second table, a third oracle: tzdata's
  `leap-seconds.list`, read here line by line, apart from the Lean code.
  `known` requests must give the SI seconds and TAI − UTC it implies,
  or NOLEAP for a second 60 it does not list. The inputs are 23:59:58,
  23:59:59, 23:59:60 and the next 00:00:00 at every month end from 1970
  to 2030, in UTC and spelled under seven offsets, and random valid
  timestamps, near misses and mutated strings, which `known` must refuse
  wherever `parse` does. `fromsi` requests take every leap second's SI seconds and
  the two seconds either side, the ends of the range and one past each,
  random numbers, and the SI seconds of random timestamps;
- for RFC 9557, the Internet Extended Date/Time Format, a fourth
  oracle: its grammar (section 4.1) and its rules for elective and
  critical tags (sections 3.2 to 3.4), written again in this script.
  `ixdtf` requests must give the printed form, whether the example
  application must treat the string as erroneous, and the first `u-ca`
  tag. The inputs are the 23 timestamps of sections 1.2, 3.3, 3.4 and
  4.2, which `Spec.ixdtf_vectors` also states, the edges of the grammar
  and rules written out below,
  random timestamps with random suffixes (time zones by name and by
  offset, tags with known, unknown and experimental keys, each item
  elective or critical, keys repeated), and those suffixes mutated: a
  character changed, dropped or added, brackets, `!` and `=` among them,
  the first bracket dropped or a last one left open, a key in upper
  case, `.` or `..` as a zone part, an empty item or value, a time zone
  after a tag;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF. The first 20,000 parsed strings
that can be command-line arguments are also given to `rfc3339 check`.
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


# 0000-01-01T00:00:00Z and 9999-12-31T23:59:59Z in Unix seconds.
FIRST, LAST = -62167219200, 253402300799


def unix_of(year, month, day, hour=0, minute=0, second=0):
    """Seconds since the epoch of a UTC date and time, by `datetime`."""
    moved, days = shifted(year)
    delta = datetime(moved, month, day, hour, minute, second, tzinfo=timezone.utc) - EPOCH
    return (delta.days - days) * 86400 + delta.seconds


def from_unix(n):
    """The expected answer to `fromunix n`: the UTC timestamp, by
    `datetime` arithmetic, or NONE outside years 0000 to 9999."""
    if not FIRST <= n <= LAST:
        return "NONE"
    shift = 0
    if n < unix_of(2, 1, 1):
        n, shift = n + CYCLE_DAYS * 86400, 400
    d = EPOCH + timedelta(seconds=n)
    return (f"{d.year - shift:04d}-{d.month:02d}-{d.day:02d}T"
            f"{d.hour:02d}:{d.minute:02d}:{d.second:02d}Z")


# The leap second table: tzdata's leap-seconds.list, read here, apart from
# the Lean code. Each line: an NTP time, and TAI - UTC from then on.
LEAP_FILE = Path("/usr/share/zoneinfo/leap-seconds.list")
NTP_UNIX = 2208988800
EPOCH_1972 = 63072000


def leap_table():
    if not LEAP_FILE.exists():
        sys.exit(f"needs tzdata's {LEAP_FILE}, the leap second table the tests check against")
    rows, expires = [], None
    for line in LEAP_FILE.read_text().splitlines():
        if line.startswith("#$"):
            LEAP_FILE_INFO["updated"] = int(line.split()[1])
        elif line.startswith("#h"):
            LEAP_FILE_INFO["hash"] = " ".join(line.split()[1:])
        elif line.startswith("#@"):
            expires = int(line.split()[1])
        elif line.strip() and not line.startswith("#"):
            ntp, off = line.split()[:2]
            rows.append((int(ntp), int(off)))
    return rows, expires


LEAP_FILE_INFO = {}
LEAP_TABLE, LEAP_EXPIRES = leap_table()
# The Unix seconds of the midnight after each leap second, which is also
# what Unix seconds give the leap second itself.
LEAP_MIDNIGHTS = [ntp - NTP_UNIX for ntp, _ in LEAP_TABLE[1:]]
# The SI seconds since 1972 of each leap second.
LEAP_SI = [m - EPOCH_1972 + i for i, m in enumerate(LEAP_MIDNIGHTS)]


def known(s):
    """The expected answer to `known`: SI seconds since 1972 and TAI - UTC
    by the table, NOLEAP for a second 60 the table does not list, or
    REJECT."""
    f = reference(s)
    if f is None:
        return "REJECT"
    u = f["unix"]
    if f["second"] == 60:
        if u not in LEAP_MIDNIGHTS:
            return "NOLEAP"
        before = LEAP_MIDNIGHTS.index(u)
        tai = LEAP_TABLE[before][1]
    else:
        before = sum(1 for m in LEAP_MIDNIGHTS if m <= u)
        tai = max((off for ntp, off in LEAP_TABLE if ntp <= u + NTP_UNIX), default=None)
    return f"OK\t{u - EPOCH_1972 + before}\t{tai if u >= EPOCH_1972 else '-'}"


def from_si(n):
    """The expected answer to `fromsi n`, by the table and `from_unix`."""
    if n < 0:
        return "NONE"
    k = sum(1 for x in LEAP_SI if x < n)
    if n in LEAP_SI:
        r = from_unix(n + EPOCH_1972 - k - 1)
        return r if r == "NONE" else r[:17] + "60" + r[19:]
    return from_unix(n + EPOCH_1972 - k)


def month_end_grid():
    """23:59:58 to the next 00:00:00 at every month end from 1970 to 2030,
    in UTC and spelled under other offsets."""
    for year in range(1970, 2031):
        for month in range(1, 13):
            last = month_length(year, month)
            base = datetime(year, month, last, 23, 59)
            for off in (0, 60, -480, 330, 1439, -1439, 765):
                local = base + timedelta(minutes=off)
                text = "Z" if off == 0 else (f"+{off // 60:02d}:{off % 60:02d}" if off > 0 else
                                             f"-{-off // 60:02d}:{-off % 60:02d}")
                for sec in (58, 59, 60):
                    yield stamp(local.year, local.month, local.day, local.hour, local.minute,
                                sec, "", text)
                nxt = local + timedelta(minutes=1)
                yield stamp(nxt.year, nxt.month, nxt.day, nxt.hour, nxt.minute, 0, "", text)


def si_grid():
    for x in LEAP_SI:
        yield from (x - 2, x - 1, x, x + 1, x + 2)
    top = LAST - EPOCH_1972 + len(LEAP_SI)
    yield from (-1, 0, 1, top - 1, top, top + 1, 10 ** 20, -10 ** 20)


# RFC 9557: the grammar of section 4.1 and the rules of sections 3.2 to
# 3.4, written here apart from the Lean code.
IX_ITEMS = re.compile(r"(?:\[[^\[\]]*\])*")
IX_ZONE_PART = re.compile(r"[A-Za-z._][A-Za-z0-9._+\-]*")
IX_OFFSET = re.compile(r"[+-]([0-9]{2}):([0-9]{2})")
IX_TAG = re.compile(r"([a-z_][a-z0-9_\-]*)=([A-Za-z0-9]+(?:-[A-Za-z0-9]+)*)")
# The example application of Spec.exampleProcessor.
IX_CALENDARS = (["chinese"], ["japanese"], ["hebrew"])
IX_ZONES = {"Europe/Paris": 120, "Europe/London": 60, "America/Los_Angeles": -480}


def ix_zone(body):
    """The offset in minutes of a numeric time zone, the name of a named
    one, or None when the grammar refuses it."""
    m = IX_OFFSET.fullmatch(body)
    if m:
        h, mi = int(m.group(1)), int(m.group(2))
        if h > 23 or mi > 59:
            return None
        return ("offset", (h * 60 + mi) * (1 if body[0] == "+" else -1))
    parts = body.split("/")
    if all(IX_ZONE_PART.fullmatch(q) and q not in (".", "..") for q in parts):
        return ("name", body)
    return None


def ix_reference(s):
    """The fields of an IXDTF string, or None when the grammar refuses it."""
    i = s.find("[")
    dt, sfx = (s, "") if i < 0 else (s[:i], s[i:])
    f = reference(dt)
    if f is None or not IX_ITEMS.fullmatch(sfx):
        return None
    zone, tags = None, []
    for k, body in enumerate(re.findall(r"\[([^\[\]]*)\]", sfx)):
        crit = body.startswith("!")
        b = body[1:] if crit else body
        if k == 0 and "=" not in b:
            z = ix_zone(b)
            if z is None:
                return None
            zone = (crit, z)
        else:
            m = IX_TAG.fullmatch(b)
            if not m:
                return None
            tags.append((crit, m.group(1), m.group(2).split("-")))
    return f, sfx, zone, tags


def ixdtf(s):
    """The expected answer to `ixdtf`."""
    r = ix_reference(s)
    if r is None:
        return "REJECT"
    f, sfx, zone, tags = r
    asserts = f["offset"] not in ("Z", "-00:00")
    bad = False
    if zone and zone[0]:
        kind, z = zone[1]
        m = z if kind == "offset" else IX_ZONES.get(z)
        if m is None or (asserts and m != f["offset_minutes"]):
            bad = True
    for crit, key, values in tags:
        known = key == "u-ca" and values in IX_CALENDARS
        if crit and not known:
            bad = True
        if crit and any(k == key and v != values for _, k, v in tags):
            bad = True
        if key.startswith("_") and not known:
            bad = True
    cal = next(("-".join(v) for _, k, v in tags if k == "u-ca"), "-")
    return f"OK\t{f['print']}{sfx}\t{'true' if bad else 'false'}\t{cal}"


# The 23 timestamps of RFC 9557 in sections 1.2, 3.3, 3.4 and 4.2.
IX_EXAMPLES = [
    "2022-07-08T00:14:07+01:00[Europe/Paris]", "2022-07-08T00:14:07Z[Europe/Paris]",
    "2022-07-08T02:14:07+02:00[Europe/Paris]", "2022-07-08T00:14:07+01:00[knort=blargel]",
    "2022-07-08T00:14:07+01:00[!Europe/Paris]", "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]",
    "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]", "2022-07-08T00:14:07Z[!knort=blargel]",
    "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]", "2022-07-08T00:14:07Z[u-ca=chinese]",
    "2022-07-08T00:14:07+00:00[!Europe/London]", "2022-07-08T00:14:07+00:00[Europe/London]",
    "2022-07-08T00:14:07Z[!Europe/London]", "2022-07-08T00:14:07Z[Europe/London]",
    "1996-12-19T16:39:57-08:00", "1996-12-19T16:39:57-08:00[America/Los_Angeles]",
    "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]",
    "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]", "2022-07-08T00:14:07+08:45[+08:45]",
    # With no suffix: the string section 3.3 says its first example can be
    # treated as, and Figure 4's instant in UTC, from section 4.2's text
    "2022-07-08T00:14:07+01:00", "1996-12-20T00:39:57Z",
    # Section 1.2's two strings with no seconds. RFC 3339's date-time
    # requires them, since partial-time has time-second, so both are
    # refused.
    "2020-01-01T00:00+01:00[Europe/Paris]", "2020-01-01T00:00+01:00[+01:00]",
]
# The edges of the grammar and the rules, each written once.
IX_EDGES = [
    "2022-07-08T00:14:07Z[..]", "2022-07-08T00:14:07Z[a/..]", "2022-07-08T00:14:07Z[../a]",
    "2022-07-08T00:14:07Z[...]", "2022-07-08T00:14:07Z[.a]", "2022-07-08T00:14:07Z[a/./b]",
    "2022-07-08T00:14:07Z[+23:59]", "2022-07-08T00:14:07Z[+24:00]", "2022-07-08T00:14:07Z[-00:60]",
    "2022-07-08T00:14:07Z[!+01:00]", "2022-07-08T00:14:07+01:00[!+01:00]",
    "2022-07-08T00:14:07+02:00[!+01:00]", "2022-07-08T00:14:07-00:00[!+01:00]",
    "2022-07-08T00:14:07+00:00[!-00:00]", "2022-07-08T00:14:07-00:00[!Europe/Paris]",
    "2022-07-08T00:14:07+02:00[!Europe/Paris]", "2022-07-08T00:14:07Z[!Nowhere/Fake]",
    "2022-07-08T00:14:07Z[!u-ca=hebrew][!u-ca=hebrew]", "2022-07-08T00:14:07Z[!u-ca=hebrew][u-ca=hebrew]",
    "2022-07-08T00:14:07Z[u-ca=hebrew][u-ca=chinese][!u-ca=hebrew]", "2022-07-08T00:14:07Z[!u-ca=a-b]",
    "2022-07-08T00:14:07Z[_=x]", "2022-07-08T00:14:07Z[!_x=y]", "2022-07-08T00:14:07Z[x_=y]",
    "2022-07-08T00:14:07Z[u-ca=]", "2022-07-08T00:14:07Z[=x]", "2022-07-08T00:14:07Z[u-ca==x]",
    "2022-07-08T00:14:07Z[u-ca=x-]", "2022-07-08T00:14:07Z[u-ca=-x]", "2022-07-08T00:14:07Z[Ab=x]",
    "2022-07-08T00:14:07Z[0a=x]", "2022-07-08T00:14:07Z[-a=x]", "2022-07-08T00:14:07Z[!!u-ca=x]",
    "2022-07-08T00:14:07Z[!]", "2022-07-08T00:14:07Z[]", "2022-07-08T00:14:07Z[Europe/Paris][Europe/Paris]",
    "2022-07-08T00:14:07Z[u-ca=hebrew][Europe/Paris]", "2022-07-08T00:14:07Z[Europe/Paris]x",
    "2022-07-08T00:14:07Z [Europe/Paris]", "2022-07-08T00:14:07Z[Europe//Paris]",
    "2022-07-08T00:14:07Z[/Europe]", "2022-07-08T00:14:07Z[Europe/]", "2022-07-08T00:14:07Z[Z]",
    "2022-07-08T00:14:07Z[UTC][u-ca=hebrew]", "2022-07-08T00:14:07Z[u-ca=Hebrew]",
    "1990-12-31T23:59:60Z[u-ca=hebrew]", "2022-07-08t00:14:07z[u-ca=hebrew]",
    # A critical -00:00 zone is offset 0, whatever the timestamp's offset
    "2022-07-08T01:14:07+01:00[!-00:00]", "2022-07-07T16:14:07-08:00[!-00:00]",
    "2022-07-08T00:14:07Z[!-00:00]",
    # Critical zones that agree with an asserted offset
    "1996-12-19T16:39:57-08:00[!America/Los_Angeles]", "2022-07-08T00:14:07+08:45[!+08:45]",
    "2022-07-08T00:14:07+01:00[!+08:45]",
    # A critical tag whose key another tag uses with values that share
    # its first part, and two critical tags with one key
    "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=chinese-japanese]",
    "2022-07-08T00:14:07Z[u-ca=chinese-japanese][!u-ca=chinese]",
    "2022-07-08T00:14:07Z[!u-ca=chinese][!u-ca=japanese]",
    "2022-07-08T00:14:07Z[!u-ca=chinese][!u-ca=chinese]",
]
IX_NAMES = ["Europe/Paris", "Europe/London", "America/Los_Angeles", "Asia/Tokyo", "UTC", "Etc/GMT+5",
            "America/Argentina/Buenos_Aires", "_x", ".a", "a.b-c+d_e", "Z", "z"]
IX_KEYS = ["u-ca", "u-ca", "knort", "_foo", "x", "a-b_c9", "_"]
IX_VALUES = [["chinese"], ["japanese"], ["hebrew"], ["gregory"], ["blargel"], ["a", "b"], ["X1"], ["0"],
             ["chinese", "japanese"]]


def ix_offset_text(rng):
    """An offset as RFC 3339 writes it; 0 as `+00:00` or `-00:00`."""
    m = rng.choice([0, 60, 120, -480, 330, -1439, 1439])
    sign = "+" if m > 0 or (m == 0 and rng.random() < 0.5) else "-"
    return sign + f"{abs(m) // 60:02d}:{abs(m) % 60:02d}"


def random_suffix(rng):
    items = []
    if rng.random() < 0.6:
        flag = "!" if rng.random() < 0.3 else ""
        body = ix_offset_text(rng) if rng.random() < 0.2 else rng.choice(IX_NAMES)
        items.append(f"[{flag}{body}]")
    for _ in range(rng.choice([0, 1, 1, 2, 3])):
        flag = "!" if rng.random() < 0.3 else ""
        items.append(f"[{flag}{rng.choice(IX_KEYS)}={'-'.join(rng.choice(IX_VALUES))}]")
    return "".join(items)


def mutate_suffix(rng, sfx):
    """A suffix with one change that is likely to break the grammar."""
    op = rng.randrange(10)
    c = list(sfx)
    if op == 0 and c:
        c[rng.randrange(len(c))] = rng.choice("[]!=-/.+_aZ0 ")
    elif op == 1 and c:
        del c[rng.randrange(len(c))]
    elif op == 2:
        c.insert(rng.randint(0, len(c)), rng.choice("[]!=-/.+_aZ0"))
    elif op == 3:
        return sfx + rng.choice(["[]", "[!]", "[=x]", "[x=]", "[.]", "[..]", "[a/..]", "[a//b]"])
    elif op == 4:
        return sfx + "[U-ca=x]"
    elif op == 5:
        return sfx + "[u-ca=a--b]"
    elif op == 6:
        return sfx + "[" + rng.choice(IX_NAMES) + "]"
    elif op == 7:
        return sfx + rng.choice(["[+24:00]", "[+23:60]", "[Z]", "[+1:00]", "[!!u-ca=x]"])
    elif op == 8:
        return sfx.replace("[", "", 1)
    else:
        return sfx + "["
    return "".join(c)


def random_ixdtf(rng):
    base = random_valid(rng) if rng.random() < 0.7 else stamp(
        2022, 7, 8, 0, 14, 7, "", rng.choice(["Z", "-00:00", "+00:00", "+01:00", "+02:00", "-08:00"]))
    sfx = random_suffix(rng)
    if rng.random() < 0.3:
        sfx = mutate_suffix(rng, sfx)
    return base + sfx


def unix_grid():
    """The ends of the range and one second past each, numbers at the
    edges of 32-bit counts, and the first second of every month of years
    chosen for the leap year rule, with the seconds either side."""
    yield from (FIRST - 1, FIRST, FIRST + 1, LAST - 1, LAST, LAST + 1, 0, -1, 1,
                2 ** 31 - 1, 2 ** 31, -2 ** 31, 2 ** 32, 10 ** 20, -10 ** 20)
    for year in (0, 1, 3, 4, 99, 100, 101, 399, 400, 1582, 1600, 1700, 1800, 1900, 1969,
                 1970, 2000, 2024, 2100, 2400, 9996, 9998, 9999):
        for month in range(2, 13):
            start = unix_of(year, month, 1)
            yield from (start - 1, start, start + 1)
    # The first second of every year, and the seconds either side: where
    # a year begins against where an average year would put it.
    for year in range(10000):
        start = unix_of(year, 1, 1)
        yield from (start - 1, start, start + 1)


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
    """The place of the instant in UTC order: the UTC minute, the second
    within it (a leap second, 60, after 59), then the exact fraction."""
    minute = (f["unix"] - f["second"]) // 60
    return (minute, f["second"], Fraction(int(f["fraction"] or "0"), 10 ** len(f["fraction"])))


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
    for year in [0, 1990, 2000, 2001, 9999]:
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


def leap_pair(rng):
    """A leap second and a nearby second: second 59 before it, or the
    first second of the next minute, in the same or another offset."""
    year, month = rng.randint(1972, 2100), rng.choice([6, 12, rng.randint(1, 12)])
    last = month_length(year, month)
    frac_a, frac_b = random_fraction(rng), random_fraction(rng)
    off_a, off_b = random_offset_minutes(rng), random_offset_minutes(rng)
    leap = datetime(year, month, last, 23, 59) + timedelta(minutes=off_a)
    a = stamp(leap.year, leap.month, leap.day, leap.hour, leap.minute, 60, frac_a,
              offset_text(off_a, rng))
    if rng.random() < 0.5:
        other, sec = datetime(year, month, last, 23, 59) + timedelta(minutes=off_b), 59
    else:
        other, sec = datetime(year, month, last, 23, 59) + timedelta(minutes=1 + off_b), 0
    b = stamp(other.year, other.month, other.day, other.hour, other.minute, sec, frac_b,
              offset_text(off_b, rng))
    return (a, b) if rng.random() < 0.5 else (b, a)


def edge_grid():
    """The first and last days of the range, where an offset moves the
    UTC date outside years 0000 to 9999: local minutes near each end of
    the day and near the offset, with seconds 0, 59 and 60."""
    for year, month, day in [(0, 1, 1), (9999, 12, 31)]:
        for off in [1, -1, 61, -61, 1439, -1439]:
            a = abs(off)
            for minute_of_day in sorted({0, 1, a - 1, a, 1440 - a - 1, 1440 - a, 1438, 1439}):
                h, m = divmod(minute_of_day % 1440, 60)
                for second in (0, 59, 60):
                    sign = "+" if off > 0 else "-"
                    yield stamp(year, month, day, h, m, second, "",
                                f"{sign}{a // 60:02d}:{a % 60:02d}")


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
    ("compare 3 30", "odd hex in the first string to compare"),
    ("compare 30 3A", "upper case hex in the second string to compare"),
    ("compare 30 ff", "not UTF-8 in the second string to compare"),
    ("compare c0af 30", "an overlong encoding in the first string to compare"),
    (" parse 30", "a leading space"),
    ("parse  30", "two spaces"),
    ("fromunix", "no number"),
    ("fromunix 1 2", "two numbers"),
    ("fromunix 1_000", "an underscore"),
    ("fromunix +1", "a plus sign"),
    ("fromunix -", "a sign alone"),
    ("fromunix --1", "two signs"),
    ("fromunix 1.5", "a fraction"),
    ("fromunix 0x10", "hex"),
    ("fromunix \u0663", "a digit that is not ASCII"),
    ("known", "no argument"),
    ("known 3", "an odd number of hex digits"),
    ("known 30 30", "two arguments"),
    ("known ff", "not UTF-8"),
    ("fromsi", "no number"),
    ("fromsi +1", "a plus sign"),
    ("fromsi 1.5", "a fraction"),
    ("fromsi 1 2", "two numbers"),
    ("fromsi 1_000", "an underscore"),
    ("fromsi -", "a sign alone"),
    ("fromsi --1", "two signs"),
    ("fromsi 0x10", "hex"),
    ("fromsi \u0663", "a digit that is not ASCII"),
    ("known 3G", "not a hex digit"),
    ("known 3A", "hex digits are lower case"),
    ("known c0af", "an overlong encoding, not UTF-8"),
    ("known eda080", "a surrogate, not UTF-8"),
    ("ixdtf", "no argument"),
    ("ixdtf 3", "an odd number of hex digits"),
    ("ixdtf 30 30", "two arguments"),
    ("ixdtf ff", "not UTF-8"),
]

# Strings `known` must answer REJECT, not NOLEAP: second 60 away from a
# UTC month end, second 61, an offset out of range, and no timestamp.
KNOWN_REJECT = [
    "1990-12-30T23:59:60Z",
    "1990-12-31T23:59:61Z",
    "1990-12-31T23:59:60+24:00",
    "2015-02-30T00:00:00Z",
    "",
    "garbage",
]

# A last line with no LF must still be answered.
AT_EOF = [
    ("parse " + "1985-04-12T23:20:50.52Z".encode().hex(), None),
    ("compare " + "1990-12-31T23:59:60Z".encode().hex() + " " +
     "1991-01-01T00:00:00Z".encode().hex(), "<"),
]


def hexed(s):
    return s.encode("utf-8").hex()


def cases(seed, count):
    """(label, request, expected answer, mutated) for each input."""
    rng = random.Random(seed)
    # The short lists first, so that a run with a small count has them.
    fixed = [("error", req, "error", False) for req, _ in MALFORMED]
    for s in KNOWN_REJECT:
        assert known(s) == "REJECT", s
        fixed.append(("known", f"known {hexed(s)}", "REJECT", False))
    for s in IX_EXAMPLES + IX_EDGES:
        fixed.append(("ixdtf", f"ixdtf {hexed(s)}", ixdtf(s), False))
    for s in itertools.chain(day_grid(), leap_grid(), edge_grid()):
        fixed.append(("grid", f"parse {hexed(s)}", answer(reference(s)), False))
    edges = list(edge_grid())
    for a, b in zip(edges, edges[1:]):
        fixed.append(("compare", f"compare {hexed(a)} {hexed(b)}", order(a, b), False))
    for n in unix_grid():
        fixed.append(("fromunix", f"fromunix {n}", from_unix(n), False))
    for s in month_end_grid():
        fixed.append(("known", f"known {hexed(s)}", known(s), False))
    for n in si_grid():
        fixed.append(("fromsi", f"fromsi {n}", from_si(n), False))
    made = 0
    for item in fixed[:count]:
        yield item
        made += 1
    while made < count:
        r = rng.random()
        if r < 0.03:
            s = random_ixdtf(rng)
            yield ("ixdtf", f"ixdtf {hexed(s)}", ixdtf(s), False)
            made += 1
            continue
        if r < 0.06:
            r = rng.random()
            if r < 0.65:
                s = random_valid(rng)
            elif r < 0.8:
                s = leap_pair(rng)[0]
            elif r < 0.9:
                s = near_miss(rng)
            else:
                base = random_valid(rng)
                s = mutate(rng, base)
            yield ("known", f"known {hexed(s)}", known(s), False)
            made += 1
            continue
        if r < 0.1:
            r = rng.random()
            if r < 0.4:
                n = rng.randint(-10, LAST - EPOCH_1972 + 40)
            elif r < 0.7:
                n = rng.choice(LEAP_SI) + rng.randint(-86400, 86400)
            else:
                want = known(random_valid(rng))
                n = int(want.split("\t")[1]) if want.startswith("OK") else rng.randint(0, 10 ** 9)
            yield ("fromsi", f"fromsi {n}", from_si(n), False)
            made += 1
            continue
        if r < 0.16:
            r = rng.random()
            if r < 0.3:
                n = rng.randint(FIRST - 10 ** 7, LAST + 10 ** 7)
            elif r < 0.4:
                # Near an end of the range, on either side.
                n = rng.choice([FIRST, LAST]) + rng.randint(-10 ** 5, 10 ** 5)
            elif r < 0.7:
                # The second before, at or after a midnight.
                n = FIRST + rng.randint(-1, (LAST - FIRST) // 86400 + 1) * 86400 + rng.choice([-1, 0, 1])
            else:
                # The seconds of a valid timestamp, which name its instant.
                f = reference(random_valid(rng))
                n = f["unix"] if f else rng.randint(FIRST, LAST)
            yield ("fromunix", f"fromunix {n}", from_unix(n), False)
            made += 1
            continue
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
            r = rng.random()
            if r < 0.4:
                a, b = same_instant_pair(rng)
            elif r < 0.6:
                a, b = leap_pair(rng)
            elif r < 0.65:
                a, b = (near_miss(rng), random_valid(rng))[:: rng.choice([1, -1])]
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


def run_check(args, timeout=300):
    """Output lines and exit code of `rfc3339 check ARGS`."""
    run = subprocess.run([str(EXE), "check", *args], capture_output=True, timeout=timeout)
    return run.stdout.decode("utf-8", "backslashreplace").split("\n")[:-1], run.returncode


def check_mode(items, limit=20000, batch=500):
    """Runs `check` mode on the first `limit` parsed strings that can be
    command-line arguments, in batches, and on no arguments at all. Each
    output line must be the printed form and Unix seconds, or `invalid`
    and the string, and the exit code 1 when any string is invalid."""
    strings = []
    for label, req, _, _ in items:
        if label != "error" and req.startswith("parse ") and len(strings) < limit:
            s = bytes.fromhex(req.split(" ")[1]).decode("utf-8")
            if s and not any(c in s for c in "\x00\n\r"):
                strings.append(s)
    problems = []
    for i in range(0, len(strings), batch):
        args = strings[i:i + batch]
        want = []
        for s in args:
            f = reference(s)
            want.append(f"{f['print']}\t{f['unix']}" if f else f"invalid\t{s}")
        code_want = 1 if any(w.startswith("invalid\t") for w in want) else 0
        got, code = run_check(args)
        if got != want or code != code_want:
            bad = next((j for j, (g, w) in enumerate(zip(got, want)) if g != w), None)
            where = f"line {bad}: got {got[bad]!r}, expected {want[bad]!r}" if bad is not None else ""
            problems.append((f"check with {len(args)} arguments from {args[0]!r}",
                             f"exit {code_want}", f"exit {code} {where}".strip()))
    got, code = run_check([])
    if code != 2 or got:
        problems.append(("check with no arguments", "usage and exit 2", f"exit {code}, {got[:2]}"))
    return len(strings), problems


def oracle():
    return (f"Python {platform.python_version()} `datetime` and `calendar`, the "
            f"RFC 3339 rules copied into this script, for leap seconds tzdata's "
            f"`{LEAP_FILE}`, read by this script, and for RFC 9557 its grammar and rules "
            f"written in this script")


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
    # Every seventh request ends in CR LF, which the tool must take as LF.
    out, problem = run_tool("".join(req + ("\r\n" if i % 7 == 6 else "\n")
                                    for i, (_, req, _, _) in enumerate(items)))
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

    check_args, check_problems = check_mode(items)
    failures += check_problems

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
    from_unix_wants = [want for label, _, want, _ in items if label == "fromunix"]
    knowns = [want for label, _, want, _ in items if label == "known"]
    known_leaps = sum(1 for label, req, want, _ in items if label == "known" and
                      want.startswith("OK") and reference(bytes.fromhex(req.split(" ")[1]).decode())["second"] == 60)
    from_si_wants = [want for label, _, want, _ in items if label == "fromsi"]
    ix_wants = [want for label, _, want, _ in items if label == "ixdtf"]
    expires = datetime(1900, 1, 1) + timedelta(seconds=LEAP_EXPIRES) if LEAP_EXPIRES else None
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
        f"- Unix seconds turned back into timestamps: {len(from_unix_wants)}, of which "
        f"{from_unix_wants.count('NONE')} outside years 0000 to 9999",
        f"- Leap second table: {LEAP_FILE}, {len(LEAP_TABLE)} lines, {len(LEAP_MIDNIGHTS)} leap "
        f"seconds, expires {expires:%Y-%m-%d}, last updated at NTP time "
        f"{LEAP_FILE_INFO.get('updated')}, hash line `{LEAP_FILE_INFO.get('hash')}`"
        if expires else f"- Leap second table: {LEAP_FILE}",
        f"- Timestamps checked against the table (`known`): {len(knowns)}, of which "
        f"{known_leaps} leap seconds of the table, {knowns.count('NOLEAP')} with a second 60 it "
        f"does not list, and {knowns.count('REJECT')} rejected",
        f"- SI seconds turned back into timestamps (`fromsi`): {len(from_si_wants)}, of which "
        f"{sum(1 for w in from_si_wants if w[17:19] == '60')} leap seconds and "
        f"{from_si_wants.count('NONE')} outside 1972 to 9999",
        f"- RFC 9557 strings (`ixdtf`): {len(ix_wants)}, of which "
        f"{sum(1 for w in ix_wants if w.startswith('OK'))} read, "
        f"{sum(1 for w in ix_wants if w.startswith('OK') and w.split(chr(9))[2] == 'true')} of them "
        f"erroneous for the example application, and {ix_wants.count('REJECT')} refused",
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Strings also given to `rfc3339 check` as arguments, in batches of 500: {check_args}, "
        f"and once with no arguments",
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
