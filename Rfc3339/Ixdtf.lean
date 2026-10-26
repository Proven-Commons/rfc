/-
  RFC 9557, the Internet Extended Date/Time Format (IXDTF): reading and
  writing the suffix, and the rules for elective and critical tags.
-/

import Rfc3339.IxdtfTypes
import Rfc3339.Format

namespace Rfc3339

def isAlpha (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

def isDigitChar (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `time-zone-part`: a letter, `.` or `_`, then letters, digits, `.`,
    `_`, `-` and `+`; but not `.` or `..`. -/
def zonePartOK : List Char → Bool
  | [] => false
  | c :: cs =>
    (isAlpha c || c == '.' || c == '_') &&
      cs.all (fun d => isAlpha d || isDigitChar d || d == '.' || d == '_' || d == '-' || d == '+') &&
      c :: cs != ['.'] && c :: cs != ['.', '.']

/-- `suffix-key`: a lower case letter or `_`, then lower case letters,
    digits, `_` and `-`. -/
def keyOK : List Char → Bool
  | [] => false
  | c :: cs =>
    (('a' ≤ c && c ≤ 'z') || c == '_') &&
      cs.all (fun d => ('a' ≤ d && d ≤ 'z') || d == '_' || isDigitChar d || d == '-')

/-- `suffix-value`: one or more letters and digits. -/
def valueOK (v : List Char) : Bool := !v.isEmpty && v.all (fun c => isAlpha c || isDigitChar c)

/-- The body of a time zone item, after any `!`: a numeric offset, with
    hours 00 to 23 and minutes 00 to 59, or a name. -/
def parseZone (body : List Char) : Option Zone :=
  match body with
  | '+' :: _ | '-' :: _ =>
    match parseOffset body with
    | some o => if o.isValid then some (.offset o) else none
    | none => none
  | _ =>
    let parts := body.splitOn '/'
    if parts.all zonePartOK then some (.name parts) else none

/-- The body of a tag, after any `!`: the key, `=`, and the values,
    separated by `-`. -/
def parseTag (critical : Bool) (body : List Char) : Option Tag :=
  let key := body.takeWhile (· ≠ '=')
  match body.drop key.length with
  | '=' :: vs =>
    let values := vs.splitOn '-'
    if keyOK key && values.all valueOK then some ⟨critical, key, values⟩ else none
  | _ => none

/-- The bracketed items of a suffix, each with its critical flag and its
    body. Each item takes at least two characters, so `fuel` equal to
    the length is enough. -/
def suffixItems : Nat → List Char → Option (List (Bool × List Char))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, c :: rest =>
    if c = '[' then
      let body := rest.takeWhile (· ≠ ']')
      match rest.drop body.length with
      | ']' :: more => do
        let tail ← suffixItems fuel more
        match body with
        | '!' :: b => pure ((true, b) :: tail)
        | b => pure ((false, b) :: tail)
      | _ => none
    else none

/-- Reads a suffix: a time zone first, if the first item has no `=`,
    then tags. -/
def parseSuffix (s : List Char) : Option (Option (Bool × Zone) × List Tag) := do
  let items ← suffixItems s.length s
  match items with
  | [] => pure (none, [])
  | (crit, body) :: rest =>
    let tags ← rest.mapM fun (c, b) => parseTag c b
    if body.contains '=' then
      let t ← parseTag crit body
      pure (none, t :: tags)
    else
      let z ← parseZone body
      pure (some (crit, z), tags)

/-- Reads an IXDTF string: an RFC 3339 `date-time`, which `parse` reads,
    then the suffix. The suffix starts at the first `[`. -/
def parseExt (s : String) : Option Ext := do
  let cs := s.toList
  let dt := cs.takeWhile (· ≠ '[')
  let stamp ← parse (String.ofList dt)
  let (zone, tags) ← parseSuffix (cs.drop dt.length)
  pure ⟨stamp, zone, tags⟩

/-- The critical flag. -/
def renderFlag (critical : Bool) : List Char := if critical then ['!'] else []

def Zone.render : Zone → List Char
  | .name parts => ['/'].intercalate parts
  | .offset o => o.render

def Tag.render (t : Tag) : List Char :=
  ['['] ++ renderFlag t.critical ++ t.key ++ ['='] ++ ['-'].intercalate t.values ++ [']']

/-- The suffix: the time zone, then the tags. -/
def Ext.renderSuffix (e : Ext) : List Char :=
  (match e.zone with
   | some (c, z) => ['['] ++ renderFlag c ++ z.render ++ [']']
   | none => []) ++
  e.tags.flatMap Tag.render

/-- The IXDTF string, with `T` and `Z` in upper case. -/
def Ext.print (e : Ext) : String := String.ofList (e.stamp.render ++ e.renderSuffix)

/-- The first tag with the key: section 3.3 has an application that does
    not handle a repeated elective key choose the first. -/
def Ext.lookup (e : Ext) (key : List Char) : Option Tag :=
  e.tags.find? (·.key == key)

/-- Whether the timestamp's offset asserts a local offset. Section 2
    makes `Z` mean the same as `-00:00`: the time in UTC is known, the
    local offset is not. -/
def assertsOffset : Offset → Bool
  | .z => false
  | .minus 0 0 => false
  | _ => true

/-- Whether the time zone agrees with the timestamp, for section 3.4:
    the zone is known, and if the timestamp asserts a local offset, the
    zone has that offset at that instant. -/
def zoneAgrees (p : Processor) (t : Timestamp) : Zone → Bool
  | .offset o => !assertsOffset t.offset || offsetMinutes o == offsetMinutes t.offset
  | .name parts =>
    match p.zoneOffset parts t with
    | some m => !assertsOffset t.offset || m == offsetMinutes t.offset
    | none => false

/-- Whether an application must treat the string as erroneous, by
    sections 3.2 to 3.4: a critical time zone that is unknown or does not
    agree with the offset; a critical tag it cannot process; a critical
    tag whose key another tag gives other values; or an experimental
    key, starting with `_`, that it does not take part in. -/
def Ext.erroneous (p : Processor) (e : Ext) : Bool :=
  (match e.zone with
   | some (true, z) => !zoneAgrees p e.stamp z
   | _ => false) ||
  e.tags.any (fun t => t.critical && !p.processes t) ||
  e.tags.any (fun t => t.critical && e.tags.any fun u => u.key == t.key && u.values != t.values) ||
  e.tags.any (fun t => t.key.head? == some '_' && !p.processes t)

end Rfc3339
