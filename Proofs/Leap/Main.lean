/-
  The leap second statements of `Spec.lean`, under the same names, from
  the lemmas in the other files of `Proofs/Leap/`. The test vectors are
  checked by evaluation.
-/

import Proofs.Leap.Table
import Proofs.Leap.Si
import Proofs.Leap.Order
import Proofs.Leap.FromSi

open Rfc3339

theorem Spec.isValidKnown_iff (t : Timestamp) :
    t.isValidKnown = true ↔ Spec.ValidKnown t :=
  Rfc3339.Proofs.Leap.isValidKnown_iff t

theorem Spec.siSeconds_eq (t : Timestamp) (h : Spec.Valid t) :
    t.siSeconds = Spec.siSeconds t :=
  Rfc3339.Proofs.Leap.siSeconds_eq t h

theorem Spec.siSeconds_order (a b : Timestamp) (ha : Spec.ValidKnown a) (hb : Spec.ValidKnown b)
    (fa : a.fraction = []) (fb : b.fraction = []) :
    compare a.siSeconds b.siSeconds = a.compareInstant b :=
  Rfc3339.Proofs.Leap.siSeconds_order a b ha hb fa fb

theorem Spec.fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Spec.siSeconds t = n :=
  Rfc3339.Proofs.Leap.fromSiSeconds_iff n t

theorem Spec.fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ :=
  Rfc3339.Proofs.Leap.fromSiSeconds_isSome n

theorem Spec.taiMinusUtc_eq (t : Timestamp) (h : Spec.Valid t) (h60 : t.second ≠ 60)
    (h72 : Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ ≤ Spec.unixSeconds t) :
    t.taiMinusUtc = Spec.taiMinusUtcAt (Spec.ntpOfUnix (Spec.unixSeconds t)) :=
  Rfc3339.Proofs.Leap.taiMinusUtc_eq t h h60 h72

theorem Spec.leap_table_vectors :
    Timestamp.isValidKnown ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = true ∧
    Timestamp.isValidKnown ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = true ∧
    Timestamp.isValidKnown ⟨2017, 1, 1, 0, 59, 60, [], .plus 1 0⟩ = true ∧
    Timestamp.isValidKnown ⟨2015, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.isValidKnown ⟨1971, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.isValidKnown ⟨2026, 12, 31, 23, 59, 60, [], .z⟩ = false ∧
    Timestamp.siSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 0 ∧
    Timestamp.siSeconds ⟨1972, 6, 30, 23, 59, 59, [], .z⟩ = 15724799 ∧
    Timestamp.siSeconds ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = 15724800 ∧
    Timestamp.siSeconds ⟨1972, 7, 1, 0, 0, 0, [], .z⟩ = 15724801 ∧
    Timestamp.siSeconds ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ = 1420156827 ∧
    Timestamp.taiMinusUtc ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨2016, 12, 31, 23, 59, 59, [], .z⟩ = 36 ∧
    Timestamp.taiMinusUtc ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ = 37 ∧
    fromSiSeconds 1420156826 = some ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ ∧
    fromSiSeconds 1420156827 = some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ ∧
    fromUnixSeconds (Timestamp.unixSeconds ⟨2016, 12, 31, 23, 59, 60, [], .z⟩) =
      some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ := by
  and_intros <;> decide +kernel
