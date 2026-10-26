/-
  The fraction comparison: `compareFraction` orders two digit lists the
  same way as their values, each scaled to the longer list's length.
  Also: a list of decimal digits reads as a number below `10 ^ length`.
-/

import Rfc3339
import Spec.Defs

namespace Rfc3339.Proofs.Fraction

open Rfc3339

/-- Reading digits after a value `x` already read: `x` is shifted left
    by the number of digits still to come. -/
theorem foldl_digits (x : Nat) (ds : List Nat) :
    List.foldl (fun acc d => 10 * acc + d) x ds = x * 10 ^ ds.length + Spec.fractionValue ds := by
  induction ds generalizing x with
  | nil => simp [Spec.fractionValue]
  | cons d ds ih =>
    simp only [Spec.fractionValue, List.foldl_cons, List.length_cons] at *
    rw [ih, ih (10 * 0 + d), Nat.pow_succ, Nat.mul_zero, Nat.zero_add, Nat.add_mul,
      Nat.add_assoc]
    congr 1
    rw [Nat.mul_comm 10 x, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ ds.length)]

theorem fractionValue_nil : Spec.fractionValue [] = 0 := rfl

theorem fractionValue_cons (d : Nat) (ds : List Nat) :
    Spec.fractionValue (d :: ds) = d * 10 ^ ds.length + Spec.fractionValue ds := by
  have h := foldl_digits d ds
  simpa [Spec.fractionValue] using h

theorem fractionValue_lt (a : List Nat) (ha : ∀ d ∈ a, d ≤ 9) :
    Spec.fractionValue a < 10 ^ a.length := by
  induction a with
  | nil => simp [fractionValue_nil]
  | cons d ds ih =>
    have hd : d ≤ 9 := ha d (by simp)
    have hds : Spec.fractionValue ds < 10 ^ ds.length := ih (fun e he => ha e (by simp [he]))
    rw [fractionValue_cons, List.length_cons, Nat.pow_succ]
    have h1 : d * 10 ^ ds.length + 10 ^ ds.length ≤ 10 ^ ds.length * 10 := by
      rw [Nat.mul_comm (10 ^ ds.length) 10, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- A digit list scaled to `k` digits stays below `10 ^ k`. -/
theorem scaled_lt (a : List Nat) (ha : ∀ d ∈ a, d ≤ 9) (k : Nat) (hk : a.length ≤ k) :
    Spec.fractionValue a * 10 ^ (k - a.length) < 10 ^ k := by
  have h := Nat.mul_lt_mul_of_pos_right (fractionValue_lt a ha)
    ((Nat.pow_pos (n := k - a.length) (by decide : 0 < 10)))
  rwa [← Nat.pow_add, Nat.add_sub_cancel' hk] at h

/-- Scaling a list with a leading digit: the digit takes the top place. -/
theorem scaled_cons (d : Nat) (ds : List Nat) (k : Nat) (hk : ds.length ≤ k) :
    Spec.fractionValue (d :: ds) * 10 ^ (k + 1 - (d :: ds).length) =
      d * 10 ^ k + Spec.fractionValue ds * 10 ^ (k - ds.length) := by
  have e : k + 1 - (d :: ds).length = k - ds.length := by simp only [List.length_cons]; omega
  rw [e, fractionValue_cons, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hk]

theorem compare_add_left (p x y : Nat) : compare (p + x) (p + y) = compare x y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
  · subst h; rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]

/-- The general form: any common length `k` at least both lengths will do. -/
theorem compareFraction_scaled (a b : List Nat) :
    (∀ d ∈ a, d ≤ 9) → (∀ d ∈ b, d ≤ 9) → ∀ k, a.length ≤ k → b.length ≤ k →
      compareFraction a b =
        compare (Spec.fractionValue a * 10 ^ (k - a.length))
                (Spec.fractionValue b * 10 ^ (k - b.length)) := by
  induction a, b using compareFraction.induct with
  | case1 =>
    intro _ _ k _ _
    simp [compareFraction, fractionValue_nil]
  | case2 as ih =>
    intro ha _ k hka _
    cases k with
    | zero => simp at hka
    | succ k =>
      have has : ∀ d ∈ as, d ≤ 9 := fun e he => ha e (by simp [he])
      have hk : as.length ≤ k := by simp at hka; omega
      rw [compareFraction, ite_eq_left rfl, scaled_cons 0 as k hk, ih has (by simp) k hk (by simp)]
      simp [fractionValue_nil]
  | case3 a as h0 =>
    intro ha _ k hka _
    cases k with
    | zero => simp at hka
    | succ k =>
      have hk : as.length ≤ k := by simp at hka; omega
      rw [compareFraction, ite_eq_right h0, scaled_cons a as k hk, fractionValue_nil, Nat.zero_mul]
      symm
      apply Nat.compare_eq_gt.mpr
      have : 0 < a * 10 ^ k := Nat.mul_pos (by omega) (Nat.pow_pos (n := k) (by decide))
      omega
  | case4 bs ih =>
    intro _ hb k _ hkb
    cases k with
    | zero => simp at hkb
    | succ k =>
      have hbs : ∀ d ∈ bs, d ≤ 9 := fun e he => hb e (by simp [he])
      have hk : bs.length ≤ k := by simp at hkb; omega
      rw [compareFraction, ite_eq_left rfl, scaled_cons 0 bs k hk, ih (by simp) hbs k (by simp) hk]
      simp [fractionValue_nil]
  | case5 b bs h0 =>
    intro _ hb k _ hkb
    cases k with
    | zero => simp at hkb
    | succ k =>
      have hk : bs.length ≤ k := by simp at hkb; omega
      rw [compareFraction, ite_eq_right h0, scaled_cons b bs k hk, fractionValue_nil, Nat.zero_mul]
      symm
      apply Nat.compare_eq_lt.mpr
      have : 0 < b * 10 ^ k := Nat.mul_pos (by omega) (Nat.pow_pos (n := k) (by decide))
      omega
  | case6 a as b bs hab =>
    intro ha hb k hka hkb
    cases k with
    | zero => simp at hka
    | succ k =>
      have has : ∀ d ∈ as, d ≤ 9 := fun e he => ha e (by simp [he])
      have hka' : as.length ≤ k := by simp at hka; omega
      have hkb' : bs.length ≤ k := by simp at hkb; omega
      rw [compareFraction, ite_eq_left hab, scaled_cons a as k hka', scaled_cons b bs k hkb']
      symm
      apply Nat.compare_eq_lt.mpr
      have hx := scaled_lt as has k hka'
      have hle : (a + 1) * 10 ^ k ≤ b * 10 ^ k := Nat.mul_le_mul_right _ hab
      rw [Nat.succ_mul] at hle
      omega
  | case7 a as b bs _ hba =>
    intro ha hb k hka hkb
    cases k with
    | zero => simp at hka
    | succ k =>
      have hbs : ∀ d ∈ bs, d ≤ 9 := fun e he => hb e (by simp [he])
      have hka' : as.length ≤ k := by simp at hka; omega
      have hkb' : bs.length ≤ k := by simp at hkb; omega
      rw [compareFraction, ite_eq_right (by omega), ite_eq_left hba, scaled_cons a as k hka',
        scaled_cons b bs k hkb']
      symm
      apply Nat.compare_eq_gt.mpr
      have hy := scaled_lt bs hbs k hkb'
      have hle : (b + 1) * 10 ^ k ≤ a * 10 ^ k := Nat.mul_le_mul_right _ hba
      rw [Nat.succ_mul] at hle
      omega
  | case8 a as b bs h1 h2 ih =>
    intro ha hb k hka hkb
    cases k with
    | zero => simp at hka
    | succ k =>
      have has : ∀ d ∈ as, d ≤ 9 := fun e he => ha e (by simp [he])
      have hbs : ∀ d ∈ bs, d ≤ 9 := fun e he => hb e (by simp [he])
      have hka' : as.length ≤ k := by simp at hka; omega
      have hkb' : bs.length ≤ k := by simp at hkb; omega
      have hab : a = b := by omega
      subst hab
      rw [compareFraction, ite_eq_right h1, ite_eq_right h2, scaled_cons a as k hka',
        scaled_cons a bs k hkb', compare_add_left, ih has hbs k hka' hkb']

theorem compareFraction_eq (a b : List Nat) (ha : ∀ d ∈ a, d ≤ 9) (hb : ∀ d ∈ b, d ≤ 9) :
    compareFraction a b =
      compare (Spec.fractionValue a * 10 ^ (max a.length b.length - a.length))
              (Spec.fractionValue b * 10 ^ (max a.length b.length - b.length)) :=
  compareFraction_scaled a b ha hb _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end Rfc3339.Proofs.Fraction
