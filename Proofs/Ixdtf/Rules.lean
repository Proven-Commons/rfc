/-
  `Ext.lookup` and `Ext.erroneous` against sections 3.2 to 3.4.
-/

import Rfc3339
import Spec.Ixdtf
import Proofs.Valid

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

theorem lookup_iff (e : Ext) (k : List Char) (t : Tag) :
    e.lookup k = some t ↔ ∃ l r, e.tags = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k := by
  sorry

theorem erroneous_iff (p : Processor) (e : Ext) :
    e.erroneous p = true ↔ Spec.MustReject p e := by
  sorry

end Rfc3339.Proofs.Ixdtf
