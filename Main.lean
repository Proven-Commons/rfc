/-
  Command line front end.

    rfc3339 check TIMESTAMP...

  prints, for each timestamp, its RFC 3339 form and its Unix seconds,
  or `invalid`, and exits with 1 when any is invalid.

    rfc3339 serve

  answers requests on standard input, one per line, for the
  differential tests. A string is sent as the hex digits of its UTF-8
  bytes, so that any character, a line break included, can be sent.

    parse HEX         prints  OK, then tab-separated: the printed form,
                      Unix seconds, year, month, day, hour, minute,
                      second, fraction digits, and offset;
                      or REJECT
    compare HEX HEX   prints  <, = or >, or REJECT when either string
                      is not a timestamp
    fromunix N        prints  the printed form of the UTC timestamp for N
                      seconds since the epoch, or NONE when it falls
                      outside the years 0000 to 9999; N is decimal, with
                      an optional leading `-`
    known HEX         prints  OK, then tab-separated: SI seconds since
                      1972-01-01T00:00:00Z and TAI - UTC (`-` before
                      1972, when TAI - UTC was not a whole number of
                      seconds); NOLEAP when the timestamp is valid but
                      its second 60 is not a leap second of the table;
                      or REJECT
    fromsi N          prints  the printed form of the UTC timestamp N SI
                      seconds after 1972-01-01T00:00:00Z, with second 60
                      at a leap second, or NONE outside 1972 to 9999

  A malformed request prints `error`: an unknown operation, hex digits
  that are not in pairs, bytes that are not UTF-8, or a number that is
  not decimal. A request line
  may end in LF or CR LF.

  Every answer comes from the proved functions in `Rfc3339/`: `parse`,
  `Timestamp.print`, `Timestamp.unixSeconds`,
  `Timestamp.compareInstant`, `fromUnixSeconds`,
  `Timestamp.isValidKnown`, `Timestamp.siSeconds`,
  `Timestamp.taiMinusUtc` and `fromSiSeconds`. The hex decoding and the request handling
  here are covered by the tests, not by a proof.
-/

import Rfc3339

open Rfc3339

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The string whose UTF-8 bytes the hex digits give. -/
def fromHex (h : String) : Option String := do
  let bs ← hexBytes h.toList
  String.fromUTF8? ⟨bs.toArray⟩

def offsetText (o : Offset) : String := String.ofList o.render

def fields (t : Timestamp) : List String :=
  [t.print, toString t.unixSeconds, toString t.year, toString t.month, toString t.day,
   toString t.hour, toString t.minute, toString t.second,
   String.join (t.fraction.map toString), offsetText t.offset]

def showOrdering : Ordering → String
  | .lt => "<"
  | .eq => "="
  | .gt => ">"

/-- A decimal number: an optional `-`, then one or more ASCII digits. -/
def decimal (s : String) : Option Int :=
  let ds := if s.startsWith "-" then s.drop 1 else s
  if !ds.isEmpty && ds.all Char.isDigit then s.toInt? else none

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["parse", h] => do
    let s ← fromHex h
    pure <| match parse s with
      | some t => "\t".intercalate ("OK" :: fields t)
      | none => "REJECT"
  | ["compare", ha, hb] => do
    let a ← fromHex ha
    let b ← fromHex hb
    pure <| match parse a, parse b with
      | some ta, some tb => showOrdering (ta.compareInstant tb)
      | _, _ => "REJECT"
  | ["fromunix", n] => do
    let s ← decimal n
    pure <| match fromUnixSeconds s with
      | some t => t.print
      | none => "NONE"
  | ["known", h] => do
    let s ← fromHex h
    pure <| match parse s with
      | some t =>
        if t.isValidKnown then
          let tai := if 63072000 ≤ t.unixSeconds then toString t.taiMinusUtc else "-"
          s!"OK\t{t.siSeconds}\t{tai}"
        else "NOLEAP"
      | none => "REJECT"
  | ["fromsi", n] => do
    let s ← decimal n
    pure <| match fromSiSeconds s with
      | some t => t.print
      | none => "NONE"
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")

def check (args : List String) : IO UInt32 := do
  let mut code : UInt32 := 0
  for s in args do
    match parse s with
    | some t => IO.println s!"{t.print}\t{t.unixSeconds}"
    | none =>
      IO.println s!"invalid\t{s}"
      code := 1
  return code

def usage : String :=
  "usage: rfc3339 check TIMESTAMP...\n       rfc3339 serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: rest@(_ :: _) => check rest
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
