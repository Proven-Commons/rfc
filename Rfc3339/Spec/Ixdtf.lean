/-
  The definitions the IXDTF statements use, written from RFC 9557, the
  Internet Extended Date/Time Format, independently of the code in
  `Rfc3339/Ixdtf.lean`. Part of the approved specification, with
  `Rfc3339/Spec.lean`, `Spec/Defs.lean` and `Rfc3339/IxdtfTypes.lean`.
-/

import Rfc3339.Spec.Defs
import Rfc3339.IxdtfTypes

open Rfc3339

/-! ## Section 4.1, the grammar

```
time-zone-initial = ALPHA / "." / "_"
time-zone-char    = time-zone-initial / DIGIT / "-" / "+"
time-zone-part    = time-zone-initial *time-zone-char
                    ; but not "." or ".."
time-zone-name    = time-zone-part *("/" time-zone-part)
time-zone         = "[" critical-flag
                        time-zone-name / time-numoffset "]"

key-initial       = lcalpha / "_"
key-char          = key-initial / DIGIT / "-"
suffix-key        = key-initial *key-char

suffix-value      = 1*alphanum
suffix-values     = suffix-value *("-" suffix-value)
suffix-tag        = "[" critical-flag
                        suffix-key "=" suffix-values "]"

suffix            = [time-zone] *suffix-tag

date-time-ext     = date-time suffix

critical-flag     = [ "!" ]

alphanum          = ALPHA / DIGIT
lcalpha           = %x61-7A
```

`date-time` and `time-numoffset` are RFC 3339's, as `Spec/Defs.lean`
gives them. In ABNF (RFC 5234, section 3.10) alternation binds more
loosely than concatenation, so the `time-zone` rule read literally is
`("[" critical-flag time-zone-name) / (time-numoffset "]")`. The intent,
which section 4.1's note ("a time-zone is syntactically similar to a
suffix-tag") and every example show, is
`"[" critical-flag (time-zone-name / time-numoffset) "]"`, and that is
what is written here.
-/

/-- `ALPHA`. -/
def Rfc3339.Spec.Alpha (c : Char) : Prop := ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

/-- `DIGIT`. -/
def Rfc3339.Spec.Digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

/-- `time-zone-part`, but not `.` or `..`. -/
def Rfc3339.Spec.ZonePart (p : List Char) : Prop :=
  ∃ c cs, p = c :: cs ∧ (Rfc3339.Spec.Alpha c ∨ c = '.' ∨ c = '_') ∧
    (∀ d ∈ cs, Rfc3339.Spec.Alpha d ∨ d = '.' ∨ d = '_' ∨ Rfc3339.Spec.Digit d ∨ d = '-' ∨ d = '+') ∧
    p ≠ ['.'] ∧ p ≠ ['.', '.']

/-- What may stand in a `time-zone`: a `time-zone-name`, one or more
    parts, or a `time-numoffset`, which is RFC 3339's numeric offset, not
    `Z`. -/
def Rfc3339.Spec.ZoneValid : Zone → Prop
  | .name parts => parts ≠ [] ∧ ∀ p ∈ parts, Rfc3339.Spec.ZonePart p
  | .offset o => o ≠ .z ∧ Rfc3339.Spec.OffsetValid o

/-- `suffix-key`. -/
def Rfc3339.Spec.SuffixKey (k : List Char) : Prop :=
  ∃ c cs, k = c :: cs ∧ (('a' ≤ c ∧ c ≤ 'z') ∨ c = '_') ∧
    ∀ d ∈ cs, ('a' ≤ d ∧ d ≤ 'z') ∨ d = '_' ∨ Rfc3339.Spec.Digit d ∨ d = '-'

/-- `suffix-value`. -/
def Rfc3339.Spec.SuffixValue (v : List Char) : Prop := v ≠ [] ∧ ∀ c ∈ v, Rfc3339.Spec.Alpha c ∨ Rfc3339.Spec.Digit c

/-- A `suffix-tag`'s key and values. -/
def Rfc3339.Spec.TagValid (t : Tag) : Prop :=
  Rfc3339.Spec.SuffixKey t.key ∧ t.values ≠ [] ∧ ∀ v ∈ t.values, Rfc3339.Spec.SuffixValue v

/-- An IXDTF timestamp the grammar allows: a valid RFC 3339 timestamp, a
    time zone of the grammar if there is one, and tags of the grammar. -/
def Rfc3339.Spec.ExtValid (e : Ext) : Prop :=
  Rfc3339.Spec.Valid e.stamp ∧ (∀ c z, e.zone = some (c, z) → Rfc3339.Spec.ZoneValid z) ∧
    ∀ t ∈ e.tags, Rfc3339.Spec.TagValid t

/-- `critical-flag`. -/
def Rfc3339.Spec.renderFlag (c : Bool) : List Char := if c then ['!'] else []

/-- A `time-zone-name`, its parts joined by `/`, or a `time-numoffset`. -/
def Rfc3339.Spec.renderZone : Zone → List Char
  | .name parts => (parts.intersperse ['/']).flatten
  | .offset o => Rfc3339.Spec.renderOffset o

/-- `suffix-tag`. -/
def Rfc3339.Spec.renderTag (t : Tag) : List Char :=
  ['['] ++ Rfc3339.Spec.renderFlag t.critical ++ t.key ++ ['='] ++ (t.values.intersperse ['-']).flatten ++
    [']']

/-- `suffix`: the `time-zone`, if any, then the tags. -/
def Rfc3339.Spec.renderSuffix (e : Ext) : List Char :=
  (match e.zone with
   | some (c, z) => ['['] ++ Rfc3339.Spec.renderFlag c ++ Rfc3339.Spec.renderZone z ++ [']']
   | none => []) ++
  (e.tags.map Rfc3339.Spec.renderTag).flatten

example : Rfc3339.Spec.renderSuffix ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
      some (false, .name ["America".toList, "Los_Angeles".toList]),
      [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩ =
    "[America/Los_Angeles][u-ca=hebrew]".toList := by decide

/-! ## Sections 2, 3.2, 3.3 and 3.4: what an application must reject

Section 2 updates RFC 3339: "If the time in UTC is known, but the offset
to local time is unknown, this can be represented with an offset of
`Z`", and section 3.4 adds that "-00:00 may be used instead of Z because
they have the same meaning". So `Z` and `-00:00` assert no local offset.

Section 3.4: "In case of an inconsistency between time-offset and time
zone suffix, if the critical flag is used on the time zone suffix, an
application MUST act on the inconsistency." Figure 2's
`2022-07-08T00:14:07Z[!Europe/London]` is "not inconsistent because
[it does] not assert any particular local time nor local offset".
Section 4.1: recipients "may not be aware of such an IANA Time Zone name
and should treat such a situation as any other inconsistency."

Section 3.3: "A suffix tag may also indicate that it is critical: The
recipient is advised that it MUST NOT act on the IXDTF string unless it
can process the suffix tag as specified." Its examples
`2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]` and
`2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]` "have an internal
inconsistency ... that is marked as critical, so a recipient MUST treat
these IXDTF strings as erroneous". And: "An application that encounters
duplicate use of a suffix key in elective suffixes and does not want to
perform additional processing on this inconsistency MUST choose the
first suffix that has that key".

Section 3.2: "Key names that start with an underscore are intended for
experiments in controlled environments and cannot be registered; such
keys MUST NOT be used for interchange and MUST be rejected by
implementations not specifically configured to take part in such an
experiment."

Below, what the application can act on is a `Processor`: which tags it
processes, which taking part in an experiment means for a key that
starts with `_`, and the offset a named time zone has at an instant.
-/

/-- The timestamp's offset asserts a local offset: it is not `Z` or
    `-00:00`. -/
def Rfc3339.Spec.AssertsOffset (o : Offset) : Prop := o ≠ .z ∧ o ≠ .minus 0 0

/-- The time zone is consistent with the timestamp, for an application
    that knows the zone offsets `p` gives: the zone is known and, where
    the timestamp asserts a local offset, has that offset. -/
def Rfc3339.Spec.ZoneConsistent (p : Processor) (t : Timestamp) : Zone → Prop
  | .offset o => Rfc3339.Spec.AssertsOffset t.offset → Rfc3339.Spec.offsetMinutes o = Rfc3339.Spec.offsetMinutes t.offset
  | .name parts =>
    ∃ m, p.zoneOffset parts t = some m ∧
      (Rfc3339.Spec.AssertsOffset t.offset → m = Rfc3339.Spec.offsetMinutes t.offset)

/-- The application must treat the string as erroneous: by section 3.4,
    a critical time zone that is not consistent with the timestamp; by
    section 3.3, a critical tag it cannot process, or a critical tag
    whose key a tag uses with other values; by section 3.2, a key for an
    experiment it does not take part in. -/
def Rfc3339.Spec.MustReject (p : Processor) (e : Ext) : Prop :=
  (∃ z, e.zone = some (true, z) ∧ ¬ Rfc3339.Spec.ZoneConsistent p e.stamp z) ∨
  (∃ t ∈ e.tags, t.critical = true ∧ p.processes t = false) ∨
  (∃ t ∈ e.tags, t.critical = true ∧ ∃ u ∈ e.tags, u.key = t.key ∧ u.values ≠ t.values) ∨
  (∃ t ∈ e.tags, t.key.head? = some '_' ∧ p.processes t = false)

/-- An application for the examples of sections 3.3, 3.4 and 4.2: it
    processes `u-ca` with the calendars `chinese`, `japanese` and
    `hebrew`, takes part in no experiment, and knows three zones, with
    the offsets they had at the examples' instants: Europe/Paris +02:00
    and Europe/London +01:00 in July 2022, America/Los_Angeles -08:00 in
    December 1996. -/
def Rfc3339.Spec.exampleProcessor : Processor where
  processes t := t.key = "u-ca".toList ∧
    (t.values = ["chinese".toList] ∨ t.values = ["japanese".toList] ∨
      t.values = ["hebrew".toList])
  zoneOffset parts _ :=
    if parts = ["Europe".toList, "Paris".toList] then some 120
    else if parts = ["Europe".toList, "London".toList] then some 60
    else if parts = ["America".toList, "Los_Angeles".toList] then some (-480)
    else none
