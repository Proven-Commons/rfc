/-
  What a timestamp is: the values the parser produces and the printer
  takes. Part of the approved specification, with `Rfc3339/Spec.lean` and
  `Spec/Defs.lean`, since every statement is about these types.

  A value holds each field of an RFC 3339 `date-time` as a number,
  exactly as written. Which values are valid is `Rfc3339.Spec.Valid`, in
  `Spec/Defs.lean`.
-/

namespace Rfc3339

/-- The `time-offset` of RFC 3339, section 5.6. `-00:00` is kept apart
    from `+00:00` and `Z`: section 4.3 gives it its own meaning, an
    unknown local offset. -/
inductive Offset where
  /-- `Z`: UTC. -/
  | z
  /-- `+hh:mm`: local time is ahead of UTC by this much. -/
  | plus (hour minute : Nat)
  /-- `-hh:mm`: local time is behind UTC by this much. -/
  | minus (hour minute : Nat)
  deriving DecidableEq, Repr

/-- An RFC 3339 `date-time`: the date and time as written, in the local
    time of its offset. -/
structure Timestamp where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  /-- The digits after the decimal point, most significant first, each
      0 to 9. Empty when the string has no fraction. -/
  fraction : List Nat
  offset : Offset
  deriving DecidableEq, Repr

end Rfc3339
