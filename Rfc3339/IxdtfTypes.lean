/-
  What an RFC 9557 (IXDTF) timestamp is: an RFC 3339 timestamp, then a
  time zone and tags in brackets. Part of the approved specification,
  with `Rfc3339/Spec.lean` and `Spec/Ixdtf.lean`, since the IXDTF statements are
  about these types.
-/

import Rfc3339.Types

namespace Rfc3339

/-- The time zone in a suffix: a time zone name, kept as the parts
    between its slashes, or a numeric offset (`time-numoffset`). -/
inductive Zone where
  | name (parts : List (List Char))
  | offset (o : Offset)
  deriving DecidableEq, Repr

/-- A suffix tag: whether it is marked critical with `!`, its key, and
    its values, the parts between its hyphens. -/
structure Tag where
  critical : Bool
  key : List Char
  values : List (List Char)
  deriving DecidableEq, Repr

/-- An IXDTF timestamp: the RFC 3339 timestamp, the time zone if there
    is one with whether it is critical, and the tags in order. -/
structure Ext where
  stamp : Timestamp
  zone : Option (Bool × Zone)
  tags : List Tag
  deriving DecidableEq, Repr

/-- What an application can act on, for the rules of sections 3.3 and
    3.4: the tags it can process, and for a time zone name, the offset in
    minutes the zone has at a given instant, or `none` when it does not
    know the zone. -/
structure Processor where
  processes : Tag → Bool
  zoneOffset : List (List Char) → Timestamp → Option Int

end Rfc3339
