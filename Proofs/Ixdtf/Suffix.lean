/-
  The suffix parser against the grammar of RFC 9557, section 4.1.
-/

import Rfc3339
import Spec.Ixdtf

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

/-- `parseSuffix` reads exactly the suffixes of the grammar, as
    `Spec.renderSuffix` writes them. -/
theorem parseSuffix_iff (cs : List Char) (e : Ext) :
    parseSuffix cs = some (e.zone, e.tags) ↔
      ((∀ c z, e.zone = some (c, z) → Spec.ZoneValid z) ∧ ∀ t ∈ e.tags, Spec.TagValid t) ∧
        cs = Spec.renderSuffix e := by
  sorry

/-- The code's rendering of the suffix is the spec's. -/
theorem renderSuffix_eq (e : Ext) (h : ∀ c z, e.zone = some (c, z) → Spec.ZoneValid z) :
    e.renderSuffix = Spec.renderSuffix e := by
  sorry

/-- A suffix of the grammar is empty or starts with `[`, and holds no
    other `[` than at the start of each item; in particular a rendered
    suffix starts with `[` when it is not empty. -/
theorem renderSuffix_head (e : Ext) :
    Spec.renderSuffix e = [] ∨ (Spec.renderSuffix e).head? = some '[' := by
  sorry

end Rfc3339.Proofs.Ixdtf
