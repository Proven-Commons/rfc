/-
  The calendar code in `Rfc3339/Calendar.lean` and `Rfc3339/Instant.lean`
  agrees with the definitions in `Spec/Defs.lean`: leap years, month
  lengths, offsets in minutes, and the closed form of the day number.
-/

import Rfc3339
import Rfc3339.Spec.Defs

namespace Rfc3339.Proofs.DayNumber

open Rfc3339

theorem isLeapYear_eq (y : Nat) : isLeapYear y = Rfc3339.Spec.isLeapYear y := by
  unfold isLeapYear Rfc3339.Spec.isLeapYear
  by_cases h4 : y % 4 = 0 <;> by_cases h100 : y % 100 = 0 <;> by_cases h400 : y % 400 = 0 <;>
    simp [h4, h100, h400]

theorem daysInMonth_eq (y m : Nat) : daysInMonth y m = Rfc3339.Spec.daysInMonth y m := by
  unfold daysInMonth Rfc3339.Spec.daysInMonth
  rw [isLeapYear_eq]
  match m with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => simp
  | n + 13 =>
    have : ¬ (n + 13 = 2) := by omega
    have : ¬ (n + 13 = 4 ∨ n + 13 = 6 ∨ n + 13 = 9 ∨ n + 13 = 11) := by omega
    have : ¬ (1 ≤ n + 13 ∧ n + 13 ≤ 12) := by omega
    simp_all

theorem offsetMinutes_eq (o : Offset) : offsetMinutes o = Rfc3339.Spec.offsetMinutes o := by
  cases o <;> simp [offsetMinutes, Rfc3339.Spec.offsetMinutes]

/-- One more year adds that year's length. -/
theorem daysBeforeYear_succ (y : Nat) :
    daysBeforeYear (y + 1) = daysBeforeYear y + Rfc3339.Spec.yearLength y := by
  unfold daysBeforeYear Rfc3339.Spec.yearLength
  by_cases h4 : y % 4 = 0
  · by_cases h100 : y % 100 = 0
    · by_cases h400 : y % 400 = 0
      · have hl : Rfc3339.Spec.isLeapYear y = true := by simp [Rfc3339.Spec.isLeapYear, h4, h400]
        simp only [hl, ite_true]
        omega
      · have hl : Rfc3339.Spec.isLeapYear y = false := by simp [Rfc3339.Spec.isLeapYear, h100, h400]
        simp only [hl, Bool.false_eq_true, ite_false]
        omega
    · have hl : Rfc3339.Spec.isLeapYear y = true := by simp [Rfc3339.Spec.isLeapYear, h4, h100]
      simp only [hl, ite_true]
      omega
  · have hl : Rfc3339.Spec.isLeapYear y = false := by simp [Rfc3339.Spec.isLeapYear, h4]
    simp only [hl, Bool.false_eq_true, ite_false]
    omega

theorem daysBeforeYear_eq (y : Nat) :
    daysBeforeYear y = ((List.range y).map Rfc3339.Spec.yearLength).sum := by
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [daysBeforeYear_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem daysBeforeMonth_eq (y m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    daysBeforeMonth y m = ((List.range (m - 1)).map fun i => Rfc3339.Spec.daysInMonth y (i + 1)).sum := by
  unfold daysBeforeMonth
  rw [isLeapYear_eq]
  cases hl : Rfc3339.Spec.isLeapYear y <;>
  match m, h1, h2 with
  | 1, _, _ | 2, _, _ | 3, _, _ | 4, _, _ | 5, _, _ | 6, _, _
  | 7, _, _ | 8, _, _ | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ =>
    simp [List.range_succ, Rfc3339.Spec.daysInMonth, hl]

theorem dayNumber_eq (y m d : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    dayNumber y m d = Rfc3339.Spec.dayNumber y m d := by
  unfold dayNumber Rfc3339.Spec.dayNumber
  rw [daysBeforeYear_eq, daysBeforeMonth_eq y m h1 h2]

end Rfc3339.Proofs.DayNumber
