/-
  The instant code in `Rfc3339/Instant.lean` agrees with the definitions
  in `Spec/Defs.lean`: `unixSeconds` counts the same whole seconds as
  `Spec.unixSeconds`, `utcMinute` is `Spec.utcMinute`, and
  `compareInstant` orders two valid timestamps the same way as
  `Spec.compareInstants`.
-/

import Rfc3339
import Spec.Defs
import Proofs.DayNumber
import Proofs.Fraction

namespace Rfc3339.Proofs.Instant

open Rfc3339

/-- 1970-01-01 is day 719528. -/
theorem dayNumber_epoch : Spec.dayNumber 1970 1 1 = 719528 := by decide +kernel

theorem utcMinute_eq (t : Timestamp) (h : Spec.Valid t) :
    t.utcMinute = Spec.utcMinute t := by
  obtain ⟨_, hm1, hm2, _⟩ := h
  unfold Timestamp.utcMinute Spec.utcMinute
  rw [DayNumber.dayNumber_eq _ _ _ hm1 hm2, DayNumber.offsetMinutes_eq]

theorem unixSeconds_eq (t : Timestamp) (h : Spec.Valid t) :
    t.unixSeconds = Spec.unixSeconds t := by
  obtain ⟨_, hm1, hm2, _⟩ := h
  unfold Timestamp.unixSeconds Spec.unixSeconds Spec.utcMinute
  rw [DayNumber.dayNumber_eq _ _ _ hm1 hm2, DayNumber.offsetMinutes_eq, dayNumber_epoch]
  omega

/-- Comparing natural numbers gives the same answer as integers. -/
theorem compare_natCast (m n : Nat) : compare (m : Int) (n : Int) = compare m n := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · rw [Nat.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]
  · subst h; rw [Nat.compare_eq_eq.mpr rfl, Int.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]

/-- Adding the same number to both sides leaves the comparison alone. -/
theorem compare_add_left (p x y : Int) : compare (p + x) (p + y) = compare x y := by
  rcases Int.lt_trichotomy x y with h | h | h
  · rw [Int.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]
  · subst h; rw [Int.compare_eq_eq.mpr rfl, Int.compare_eq_eq.mpr rfl]
  · rw [Int.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]

/-- `u * P + x` against `v * P + y`, with `x` and `y` from 0 to below
    `P`: the whole parts `u` and `v` decide, unless they are equal, and
    then `x` and `y` do. -/
theorem compare_scaled (u v P x y : Int) (hx0 : 0 ≤ x) (hxP : x < P) (hy0 : 0 ≤ y)
    (hyP : y < P) :
    compare (u * P + x) (v * P + y) =
      match compare u v with
      | .eq => compare x y
      | o => o := by
  rcases Int.lt_trichotomy u v with h | h | h
  · rw [Int.compare_eq_lt.mpr h]
    apply Int.compare_eq_lt.mpr
    have hle : (u + 1) * P ≤ v * P := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    rw [Int.add_mul, Int.one_mul] at hle
    omega
  · subst h
    rw [Int.compare_eq_eq.mpr rfl, compare_add_left]
  · rw [Int.compare_eq_gt.mpr h]
    apply Int.compare_eq_gt.mpr
    have hle : (v + 1) * P ≤ u * P := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    rw [Int.add_mul, Int.one_mul] at hle
    omega

theorem compareInstant_eq (a b : Timestamp) (ha : Spec.Valid a) (hb : Spec.Valid b) :
    a.compareInstant b = Spec.compareInstants a b := by
  have hfa : ∀ d ∈ a.fraction, d ≤ 9 := ha.2.2.2.2.2.2.2.2.2.1
  have hfb : ∀ d ∈ b.fraction, d ≤ 9 := hb.2.2.2.2.2.2.2.2.2.1
  have la := Fraction.scaled_lt a.fraction hfa (max a.fraction.length b.fraction.length)
    (Nat.le_max_left _ _)
  have lb := Fraction.scaled_lt b.fraction hfb (max a.fraction.length b.fraction.length)
    (Nat.le_max_right _ _)
  have ea : (Spec.fractionValue a.fraction : Int) *
      10 ^ (max a.fraction.length b.fraction.length - a.fraction.length) =
      ((Spec.fractionValue a.fraction *
        10 ^ (max a.fraction.length b.fraction.length - a.fraction.length) : Nat) : Int) := by
    push_cast; rfl
  have eb : (Spec.fractionValue b.fraction : Int) *
      10 ^ (max a.fraction.length b.fraction.length - b.fraction.length) =
      ((Spec.fractionValue b.fraction *
        10 ^ (max a.fraction.length b.fraction.length - b.fraction.length) : Nat) : Int) := by
    push_cast; rfl
  have eP : ((10 ^ max a.fraction.length b.fraction.length : Nat) : Int) =
      (10 : Int) ^ max a.fraction.length b.fraction.length := by
    push_cast; rfl
  unfold Timestamp.compareInstant Spec.compareInstants Spec.instantKey
  simp only
  rw [utcMinute_eq a ha, utcMinute_eq b hb, Fraction.compareFraction_eq _ _ hfa hfb, ea, eb,
    compare_scaled (Spec.utcMinute a * 61 + a.second) (Spec.utcMinute b * 61 + b.second)
      ((10 : Int) ^ max a.fraction.length b.fraction.length) _ _ (by omega)
      (by rw [← eP]; omega) (by omega) (by rw [← eP]; omega), compare_natCast]
  cases compare (Spec.utcMinute a * 61 + a.second) (Spec.utcMinute b * 61 + b.second) <;> rfl

end Rfc3339.Proofs.Instant
