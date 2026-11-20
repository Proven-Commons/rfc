/-
  `Ext.lookup` and `Ext.erroneous` against sections 3.2 to 3.4.
-/

import Rfc3339
import Rfc3339.Spec.Ixdtf
import Rfc3339.Proofs.Valid

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

private theorem rx_find_iff (k : List Char) (t : Tag) : ∀ (ts : List Tag),
    ts.find? (fun u => u.key == k) = some t ↔ ∃ l r, ts = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k
  | [] => by simp
  | u :: us => by
    rw [List.find?_cons]
    by_cases h : u.key = k
    · simp only [h, beq_self_eq_true, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨[], us, by simp, h, by simp⟩
      · rintro ⟨l, r, hl, hk, hu⟩
        cases l with
        | nil => simp at hl; exact hl.1
        | cons a l =>
          simp at hl
          exact absurd (hl.1 ▸ h) (hu a (by simp))
    · have hb : (u.key == k) = false := by simpa using h
      rw [hb]
      simp only
      rw [rx_find_iff k t us]
      constructor
      · rintro ⟨l, r, hl, hk, hu⟩
        refine ⟨u :: l, r, by simp [hl], hk, ?_⟩
        intro v hv
        simp at hv
        rcases hv with rfl | hv
        · exact h
        · exact hu v hv
      · rintro ⟨l, r, hl, hk, hu⟩
        cases l with
        | nil =>
          simp at hl
          exact absurd (hl.1 ▸ hk) h
        | cons a l =>
          simp at hl
          exact ⟨l, r, hl.2, hk, fun v hv => hu v (by simp [hv])⟩

theorem lookup_iff (e : Ext) (k : List Char) (t : Tag) :
    e.lookup k = some t ↔ ∃ l r, e.tags = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k := by
  exact rx_find_iff k t e.tags


private theorem rx_assertsOffset_iff (o : Offset) : assertsOffset o = true ↔ Rfc3339.Spec.AssertsOffset o := by
  cases o with
  | z => simp [assertsOffset, Rfc3339.Spec.AssertsOffset]
  | plus h m => simp [assertsOffset, Rfc3339.Spec.AssertsOffset]
  | minus h m =>
    by_cases hh : h = 0 <;> by_cases hm : m = 0 <;> subst_vars <;>
      simp_all [assertsOffset, Rfc3339.Spec.AssertsOffset]

private theorem rx_zoneAgrees_iff (p : Processor) (t : Timestamp) (z : Zone) :
    zoneAgrees p t z = true ↔ Rfc3339.Spec.ZoneConsistent p t z := by
  cases z with
  | offset o =>
    simp only [zoneAgrees, Rfc3339.Spec.ZoneConsistent, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
      Rfc3339.Proofs.Valid.offsetMinutes_eq, ← rx_assertsOffset_iff]
    cases assertsOffset t.offset <;> simp
  | name parts =>
    simp only [zoneAgrees, Rfc3339.Spec.ZoneConsistent]
    cases hz : p.zoneOffset parts t with
    | none => simp
    | some m =>
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Rfc3339.Proofs.Valid.offsetMinutes_eq,
        ← rx_assertsOffset_iff, Option.some.injEq, exists_eq_left']
      cases assertsOffset t.offset <;> simp

theorem erroneous_iff (p : Processor) (e : Ext) :
    e.erroneous p = true ↔ Rfc3339.Spec.MustReject p e := by
  simp only [Ext.erroneous, Rfc3339.Spec.MustReject, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, or_assoc]
  apply or_congr _ Iff.rfl
  rcases h : e.zone with _ | ⟨_ | _, z⟩
  · simp
  · simp
  · simp [← rx_zoneAgrees_iff]

end Rfc3339.Proofs.Ixdtf
