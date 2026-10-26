/-
  `parseExt` and `Ext.print` against the grammar.
-/

import Proofs.Ixdtf.Suffix
import Proofs.Main

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

theorem parseExt_iff (s : String) (e : Ext) :
    parseExt s = some e ↔
      Spec.ExtValid e ∧ ∃ dt, s.toList = dt ++ Spec.renderSuffix e ∧
        dt.map Spec.asciiUpper = Spec.render e.stamp := by
  sorry

theorem printExt_eq (e : Ext) (h : Spec.ExtValid e) :
    e.print.toList = Spec.render e.stamp ++ Spec.renderSuffix e := by
  sorry

theorem parseExt_print (e : Ext) (h : Spec.ExtValid e) : parseExt e.print = some e := by
  sorry

theorem parseExt_plain (s : String) (h : '[' ∉ s.toList) :
    parseExt s = (parse s).map fun t => ⟨t, none, []⟩ := by
  sorry

end Rfc3339.Proofs.Ixdtf
