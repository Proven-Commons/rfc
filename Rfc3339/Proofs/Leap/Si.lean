/-
  SI seconds and TAI − UTC against the spec.
-/

import Rfc3339.Proofs.Leap.Table

open Rfc3339

namespace Rfc3339.Proofs.Leap

/-- Filtering a mapped list counts what filtering by the composite
    predicate counts. -/
theorem si_length_filter_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    ((l.map f).filter p).length = (l.filter fun a => p (f a)).length := by
  rw [List.filter_map, List.length_map]
  rfl

theorem leapsBefore_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.leapsBefore = Rfc3339.Spec.leapsBefore t := by
  unfold Timestamp.leapsBefore Rfc3339.Spec.leapsBefore
  rw [Instant.utcMinute_eq t h]
  have h1 := si_length_filter_map leapMonths leapKey
    (fun k => decide (k < Rfc3339.Spec.utcMinute t * 61 + (t.second : Int)))
  have h2 := si_length_filter_map Rfc3339.Spec.leapTable.tail (fun e => Rfc3339.Spec.leapSecondKey e.1)
    (fun k => decide (k < Rfc3339.Spec.utcMinute t * 61 + (t.second : Int)))
  rw [leapKey_table] at h1
  rw [← h1, h2]
  rfl

theorem si_unix1972 : Rfc3339.Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 63072000 := by
  decide +kernel

theorem siSeconds_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) : t.siSeconds = Rfc3339.Spec.siSeconds t := by
  unfold Timestamp.siSeconds Rfc3339.Spec.siSeconds
  rw [Instant.unixSeconds_eq t h, si_unix1972, leapsBefore_eq t h]

/-- The shape of the table after its first line: NTP times strictly
    increasing from `n`, offsets one more each line from `c`. -/
def si_shape : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => true
  | n, c, (n', c') :: rest => decide (n < n') && c' == c + 1 && si_shape n' c' rest

theorem si_shape_lower (l : List (Nat × Nat)) :
    ∀ n c, si_shape n c l = true → ∀ e ∈ l, n < e.1 := by
  induction l with
  | nil => intro n c _ e he; cases he
  | cons hd rest ih =>
    intro n c hs e he
    obtain ⟨n', c'⟩ := hd
    simp only [si_shape, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    obtain ⟨⟨hn, _⟩, hr⟩ := hs
    rcases List.mem_cons.mp he with he | he
    · subst he; exact hn
    · have := ih n' c' hr e he
      omega

theorem si_lastLine (l : List (Nat × Nat)) :
    ∀ (n c : Nat) (x : Int), si_shape n c l = true → (n : Int) ≤ x →
      ((((n, c) :: l).filter fun e => decide ((e.1 : Int) ≤ x)).getLast?.map (·.2)).getD 0 =
        c + (l.filter fun e => decide ((e.1 : Int) ≤ x)).length := by
  induction l with
  | nil =>
    intro n c x _ hx
    simp [hx]
  | cons hd rest ih =>
    intro n c x hs hx
    obtain ⟨n', c'⟩ := hd
    have hs' := hs
    simp only [si_shape, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs'
    obtain ⟨⟨hn, hc⟩, hr⟩ := hs'
    by_cases hx' : (n' : Int) ≤ x
    · have ih' := ih n' c' x hr hx'
      simp only [List.filter_cons, hx, hx', decide_true, ite_true] at ih' ⊢
      rw [List.getLast?_cons_cons, ih', List.length_cons]
      omega
    · have hnil : (rest.filter fun e => decide ((e.1 : Int) ≤ x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        have := si_shape_lower rest n' c' hr e he
        simp only [decide_eq_true_eq]
        omega
      simp [hx, hx', hnil]

theorem si_table_shape : si_shape 2272060800 10 Rfc3339.Spec.leapTable.tail = true := by
  decide +kernel

theorem si_table_mod : ∀ e ∈ Rfc3339.Spec.leapTable.tail, e.1 % 60 = 0 := by
  decide +kernel

theorem si_taiMinusUtcAt (x : Int) (hx : 2272060800 ≤ x) :
    Rfc3339.Spec.taiMinusUtcAt x = 10 + (Rfc3339.Spec.leapTable.tail.filter fun e => decide ((e.1 : Int) ≤ x)).length := by
  unfold Rfc3339.Spec.taiMinusUtcAt
  have hl : Rfc3339.Spec.leapTable = (2272060800, 10) :: Rfc3339.Spec.leapTable.tail := rfl
  rw [hl]
  exact si_lastLine Rfc3339.Spec.leapTable.tail 2272060800 10 x si_table_shape (by omega)

theorem taiMinusUtc_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) (h60 : t.second ≠ 60)
    (h72 : Rfc3339.Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ ≤ Rfc3339.Spec.unixSeconds t) :
    t.taiMinusUtc = Rfc3339.Spec.taiMinusUtcAt (Rfc3339.Spec.ntpOfUnix (Rfc3339.Spec.unixSeconds t)) := by
  have hs : t.second ≤ 60 := h.2.2.2.2.2.2.2.1
  rw [si_unix1972] at h72
  unfold Timestamp.taiMinusUtc
  rw [leapsBefore_eq t h, si_taiMinusUtcAt _ (by unfold Rfc3339.Spec.ntpOfUnix; omega)]
  congr 1
  unfold Rfc3339.Spec.leapsBefore
  congr 1
  apply List.filter_congr
  intro e he
  have hm := si_table_mod e he
  unfold Rfc3339.Spec.leapSecondKey Rfc3339.Spec.secondKey Rfc3339.Spec.ntpOfUnix Rfc3339.Spec.unixSeconds
  rw [Instant.dayNumber_epoch]
  simp only [decide_eq_decide]
  omega

end Rfc3339.Proofs.Leap
