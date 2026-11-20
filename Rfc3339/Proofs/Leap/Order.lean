/-
  SI seconds order known-valid whole seconds as their instants.
-/

import Rfc3339.Proofs.Leap.Table

open Rfc3339

namespace Rfc3339.Proofs.Leap

/-- Counting the entries below a threshold is monotone in the threshold. -/
private theorem or_filter_mono {α : Type} (l : List α) (f : α → Int) (x y : Int) (h : x ≤ y) :
    (l.filter fun a => decide (f a < x)).length ≤
      (l.filter fun a => decide (f a < y)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    by_cases h1 : f a < x
    · have h2 : f a < y := by omega
      simp [h1, h2] <;> omega
    · by_cases h2 : f a < y
      · simp [h1, h2] <;> omega
      · simp [h1, h2] <;> omega

/-- And strictly so when an entry lies between the two thresholds. -/
private theorem or_filter_strict {α : Type} (l : List α) (f : α → Int) (x y : Int) (h : x ≤ y)
    (z : α) (hz : z ∈ l) (hz1 : x ≤ f z) (hz2 : f z < y) :
    (l.filter fun a => decide (f a < x)).length + 1 ≤
      (l.filter fun a => decide (f a < y)).length := by
  induction l with
  | nil => simp at hz
  | cons a l ih =>
    have hm := or_filter_mono l f x y h
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hz with he | hz'
    · rw [he] at hz1 hz2
      have h1 : ¬ f a < x := by omega
      simp [h1, hz2] <;> omega
    · have ih' := ih hz'
      by_cases h1 : f a < x
      · have h2 : f a < y := by omega
        simp [h1, h2] <;> omega
      · by_cases h2 : f a < y
        · simp [h1, h2] <;> omega
        · simp [h1, h2] <;> omega

private theorem or_unix (t : Timestamp) :
    t.unixSeconds = (t.utcMinute - 719528 * 1440) * 60 + t.second := by
  unfold Timestamp.unixSeconds Timestamp.utcMinute
  omega

private theorem or_si (t : Timestamp) :
    t.siSeconds = (t.utcMinute - 719528 * 1440) * 60 + t.second - 63072000 + t.leapsBefore := by
  unfold Timestamp.siSeconds
  rw [or_unix]

private theorem or_lt (a b : Timestamp) (ha : Rfc3339.Spec.ValidKnown a) (hb : Rfc3339.Spec.ValidKnown b)
    (h : a.utcMinute * 61 + a.second < b.utcMinute * 61 + b.second) :
    a.siSeconds < b.siSeconds := by
  obtain ⟨_, _, _, _, _, _, _, hsa, _⟩ := ha.1
  obtain ⟨_, _, _, _, _, _, _, hsb, _⟩ := hb.1
  have hm : a.leapsBefore ≤ b.leapsBefore := by
    unfold Timestamp.leapsBefore
    exact or_filter_mono leapMonths leapKey _ _ (by omega)
  rw [or_si, or_si]
  by_cases h60 : a.second = 60
  · obtain ⟨ym, hym, hk⟩ := leapKey_of_known a ha h60
    have hs : a.leapsBefore + 1 ≤ b.leapsBefore := by
      unfold Timestamp.leapsBefore
      exact or_filter_strict leapMonths leapKey _ _ (by omega) ym hym (by omega) (by omega)
    omega
  · omega

private theorem or_eq (a b : Timestamp) (ha : Rfc3339.Spec.ValidKnown a) (hb : Rfc3339.Spec.ValidKnown b)
    (h : a.utcMinute * 61 + a.second = b.utcMinute * 61 + b.second) :
    a.siSeconds = b.siSeconds := by
  obtain ⟨_, _, _, _, _, _, _, hsa, _⟩ := ha.1
  obtain ⟨_, _, _, _, _, _, _, hsb, _⟩ := hb.1
  have hL : a.leapsBefore = b.leapsBefore := by
    unfold Timestamp.leapsBefore
    rw [h]
  rw [or_si, or_si, hL]
  omega

theorem siSeconds_order (a b : Timestamp) (ha : Rfc3339.Spec.ValidKnown a) (hb : Rfc3339.Spec.ValidKnown b)
    (fa : a.fraction = []) (fb : b.fraction = []) :
    compare a.siSeconds b.siSeconds = a.compareInstant b := by
  unfold Timestamp.compareInstant
  rw [fa, fb]
  rcases Int.lt_trichotomy (a.utcMinute * 61 + a.second) (b.utcMinute * 61 + b.second)
    with h | h | h
  · rw [Int.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (or_lt a b ha hb h)]
  · rw [Int.compare_eq_eq.mpr h, Int.compare_eq_eq.mpr (or_eq a b ha hb h)]
    simp [compareFraction]
  · rw [Int.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (or_lt b a hb ha h)]

end Rfc3339.Proofs.Leap
