/-
  From SI seconds back to a timestamp.
-/

import Proofs.Leap.Si
import Proofs.Leap.Order
import Proofs.FromUnix.Main

open Rfc3339

namespace Rfc3339.Proofs.Leap

theorem fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Spec.siSeconds t = n := by
  sorry

theorem fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := by
  sorry

end Rfc3339.Proofs.Leap
