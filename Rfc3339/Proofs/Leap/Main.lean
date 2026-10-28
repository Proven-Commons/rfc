/-
  The leap second statements of `Rfc3339/Spec.lean`, under the same names, from
  the lemmas in the other files of `Rfc3339/Proofs/Leap/`. The test vectors are
  checked by evaluation.
-/

import Rfc3339.Proofs.Leap.Table
import Rfc3339.Proofs.Leap.Si
import Rfc3339.Proofs.Leap.Order
import Rfc3339.Proofs.Leap.FromSi

open Rfc3339

theorem Rfc3339.Spec.isValidKnown_iff (t : Timestamp) :
    t.isValidKnown = true ↔ Rfc3339.Spec.ValidKnown t :=
  Rfc3339.Proofs.Leap.isValidKnown_iff t

theorem Rfc3339.Spec.siSeconds_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.siSeconds = Rfc3339.Spec.siSeconds t :=
  Rfc3339.Proofs.Leap.siSeconds_eq t h

theorem Rfc3339.Spec.siSeconds_order (a b : Timestamp) (ha : Rfc3339.Spec.ValidKnown a) (hb : Rfc3339.Spec.ValidKnown b)
    (fa : a.fraction = []) (fb : b.fraction = []) :
    compare a.siSeconds b.siSeconds = a.compareInstant b :=
  Rfc3339.Proofs.Leap.siSeconds_order a b ha hb fa fb

theorem Rfc3339.Spec.fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Rfc3339.Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Rfc3339.Spec.siSeconds t = n :=
  Rfc3339.Proofs.Leap.fromSiSeconds_iff n t

theorem Rfc3339.Spec.fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Rfc3339.Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ :=
  Rfc3339.Proofs.Leap.fromSiSeconds_isSome n

theorem Rfc3339.Spec.taiMinusUtc_leapsBefore (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.taiMinusUtc = 10 + Rfc3339.Spec.leapsBefore t := by
  unfold Timestamp.taiMinusUtc
  rw [Rfc3339.Proofs.Leap.leapsBefore_eq t h]

theorem Rfc3339.Spec.taiMinusUtc_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) (h60 : t.second ≠ 60)
    (h72 : Rfc3339.Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ ≤ Rfc3339.Spec.unixSeconds t) :
    t.taiMinusUtc = Rfc3339.Spec.taiMinusUtcAt (Rfc3339.Spec.ntpOfUnix (Rfc3339.Spec.unixSeconds t)) :=
  Rfc3339.Proofs.Leap.taiMinusUtc_eq t h h60 h72

theorem Rfc3339.Spec.leap_table_vectors :
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
    Timestamp.siSeconds ⟨2016, 12, 31, 23, 59, 59, [], .z⟩ = 1420156825 ∧
    Timestamp.siSeconds ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = 1420156826 ∧
    Timestamp.taiMinusUtc ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 6, 30, 23, 59, 59, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ = 10 ∧
    Timestamp.taiMinusUtc ⟨1972, 7, 1, 0, 0, 0, [], .z⟩ = 11 ∧
    Timestamp.taiMinusUtc ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ = 36 ∧
    Timestamp.taiMinusUtc ⟨2016, 12, 31, 23, 59, 59, [], .z⟩ = 36 ∧
    Timestamp.taiMinusUtc ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ = 37 ∧
    fromSiSeconds 15724800 = some ⟨1972, 6, 30, 23, 59, 60, [], .z⟩ ∧
    fromSiSeconds 1420156826 = some ⟨2016, 12, 31, 23, 59, 60, [], .z⟩ ∧
    fromSiSeconds 1420156827 = some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ ∧
    fromUnixSeconds (Timestamp.unixSeconds ⟨2016, 12, 31, 23, 59, 60, [], .z⟩) =
      some ⟨2017, 1, 1, 0, 0, 0, [], .z⟩ := by
  and_intros <;> decide +kernel
