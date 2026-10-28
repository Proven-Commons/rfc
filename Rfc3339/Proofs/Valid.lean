/-
  `Timestamp.isValid` decides exactly `Rfc3339.Spec.Valid`. The hard part is
  the leap second rule: the code's check on the local date and time
  agrees with the spec's rule that the UTC minute is the last one
  before a month begins.
-/

import Rfc3339
import Rfc3339.Spec.Defs

namespace Rfc3339.Proofs.Valid

open Rfc3339

/-! ## Small facts: the code's helpers agree with the spec's -/

theorem isLeapYear_eq (y : Nat) : isLeapYear y = Rfc3339.Spec.isLeapYear y := by
  unfold isLeapYear Rfc3339.Spec.isLeapYear
  by_cases h4 : y % 4 = 0 <;> by_cases h100 : y % 100 = 0 <;> by_cases h400 : y % 400 = 0 <;>
    simp [h4, h100, h400]

theorem daysInMonth_eq (y m : Nat) : daysInMonth y m = Rfc3339.Spec.daysInMonth y m := by
  unfold daysInMonth Rfc3339.Spec.daysInMonth
  split <;> simp_all [isLeapYear_eq] <;> omega

theorem offsetMinutes_eq (o : Offset) : offsetMinutes o = Rfc3339.Spec.offsetMinutes o := by
  cases o <;> simp [offsetMinutes, Rfc3339.Spec.offsetMinutes]

theorem offset_isValid_iff (o : Offset) : o.isValid = true ↔ Rfc3339.Spec.OffsetValid o := by
  cases o <;> simp [Offset.isValid, Rfc3339.Spec.OffsetValid]

theorem all_lt_iff (l : List Nat) : l.all (· < 10) = true ↔ ∀ d ∈ l, d ≤ 9 := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h d hd; have := h d hd; omega
  · intro h d hd; have := h d hd; omega

/-! ## Sums over ranges -/

theorem sum_range_succ (g : Nat → Nat) (k : Nat) :
    ((List.range (k + 1)).map g).sum = ((List.range k).map g).sum + g k := by
  simp [List.range_succ, List.sum_append]

theorem sum_range_mono (g : Nat → Nat) (a b : Nat) (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, sum_range_succ]
    have := ih (Nat.le_add_right _ _)
    omega

/-! ## Day numbers -/

/-- Days in the years before `y`. -/
def yearsBefore (y : Nat) : Nat := ((List.range y).map Rfc3339.Spec.yearLength).sum

/-- Days in the months before `m` of year `y`. -/
def monthsBefore (y m : Nat) : Nat :=
  ((List.range (m - 1)).map fun i => Rfc3339.Spec.daysInMonth y (i + 1)).sum

theorem dayNumber_eq (y m d : Nat) :
    Rfc3339.Spec.dayNumber y m d = yearsBefore y + monthsBefore y m + (d - 1) := rfl

theorem dayNumber_day (y m d : Nat) :
    Rfc3339.Spec.dayNumber y m d = Rfc3339.Spec.dayNumber y m 1 + (d - 1) := by
  simp only [dayNumber_eq]; omega

theorem yearsBefore_succ (y : Nat) : yearsBefore (y + 1) = yearsBefore y + Rfc3339.Spec.yearLength y := by
  unfold yearsBefore; rw [sum_range_succ]

theorem yearsBefore_mono {y y' : Nat} (h : y < y') :
    yearsBefore y + Rfc3339.Spec.yearLength y ≤ yearsBefore y' := by
  rw [← yearsBefore_succ]; exact sum_range_mono _ _ _ h

theorem monthsBefore_succ (y m : Nat) (hm : 1 ≤ m) :
    monthsBefore y (m + 1) = monthsBefore y m + Rfc3339.Spec.daysInMonth y m := by
  unfold monthsBefore
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [Nat.add_sub_cancel, Nat.add_comm 1 k]
  rw [sum_range_succ]

theorem monthsBefore_mono (y : Nat) {m m' : Nat} (h : m ≤ m') :
    monthsBefore y m ≤ monthsBefore y m' :=
  sum_range_mono _ _ _ (by omega)

theorem monthsBefore_twelve (y : Nat) : monthsBefore y 12 + 31 = Rfc3339.Spec.yearLength y := by
  cases h : Rfc3339.Spec.isLeapYear y <;>
    simp [monthsBefore, List.range_succ, Rfc3339.Spec.daysInMonth, Rfc3339.Spec.yearLength, h]

theorem daysInMonth_bounds (y m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    28 ≤ Rfc3339.Spec.daysInMonth y m ∧ Rfc3339.Spec.daysInMonth y m ≤ 31 := by
  unfold Rfc3339.Spec.daysInMonth
  split
  · split <;> omega
  · split
    · omega
    · split <;> omega

/-- A month ends within its year. -/
theorem month_end_le (y m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    monthsBefore y m + Rfc3339.Spec.daysInMonth y m ≤ Rfc3339.Spec.yearLength y := by
  rw [← monthsBefore_succ y m h1, ← monthsBefore_twelve]
  have := monthsBefore_mono y (show m + 1 ≤ 13 by omega)
  rw [show 13 = 12 + 1 from rfl, monthsBefore_succ y 12 (by decide)] at this
  have h12 : Rfc3339.Spec.daysInMonth y 12 = 31 := by simp [Rfc3339.Spec.daysInMonth]
  omega

/-- The day after the last day of month `m` is the first of month `m + 1`
    (for `m < 12`, the next month). -/
theorem next_month (y m : Nat) (h1 : 1 ≤ m) :
    Rfc3339.Spec.dayNumber y m 1 + Rfc3339.Spec.daysInMonth y m = Rfc3339.Spec.dayNumber y (m + 1) 1 := by
  simp only [dayNumber_eq, monthsBefore_succ y m h1]; omega

theorem next_year (y : Nat) :
    Rfc3339.Spec.dayNumber y 12 1 + 31 = Rfc3339.Spec.dayNumber (y + 1) 1 1 := by
  simp only [dayNumber_eq, yearsBefore_succ, ← monthsBefore_twelve y]
  simp [monthsBefore]; omega

/-- No month starts strictly inside another month. -/
theorem month_start_spaced {y m y' m' : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 12) (h1' : 1 ≤ m')
    (h2' : m' ≤ 12) (hlt : Rfc3339.Spec.dayNumber y m 1 < Rfc3339.Spec.dayNumber y' m' 1) :
    Rfc3339.Spec.dayNumber y m 1 + Rfc3339.Spec.daysInMonth y m ≤ Rfc3339.Spec.dayNumber y' m' 1 := by
  simp only [dayNumber_eq] at *
  rcases Nat.lt_trichotomy y y' with hy | rfl | hy
  · have := yearsBefore_mono hy
    have := month_end_le y m h1 h2
    omega
  · rcases Nat.lt_or_ge m m' with hm | hm
    · have := monthsBefore_mono y (show m + 1 ≤ m' from hm)
      rw [monthsBefore_succ y m h1] at this
      omega
    · have := monthsBefore_mono y hm
      omega
  · have := yearsBefore_mono hy
    have := month_end_le y' m' h1' h2'
    have := daysInMonth_bounds y' m' h1' h2'
    omega

/-! ## The leap second rule -/

/-- With the other fields in range, the code's leap second check is the
    spec's rule: the UTC minute is the last one before a month begins. -/
theorem leapSecondOK_iff (t : Timestamp) (hm1 : 1 ≤ t.month) (hm2 : t.month ≤ 12)
    (hd1 : 1 ≤ t.day) (hd2 : t.day ≤ Rfc3339.Spec.daysInMonth t.year t.month)
    (hh : t.hour ≤ 23) (hmi : t.minute ≤ 59) (ho : Rfc3339.Spec.OffsetValid t.offset) :
    leapSecondOK t = true ↔ Rfc3339.Spec.LeapSecondAllowed t := by
  obtain ⟨y, m, d, h, mi, s, f, o⟩ := t
  simp only at *
  have hob : -1439 ≤ Rfc3339.Spec.offsetMinutes o ∧ Rfc3339.Spec.offsetMinutes o ≤ 1439 := by
    cases o <;> simp [Rfc3339.Spec.offsetMinutes, Rfc3339.Spec.OffsetValid] at ho ⊢ <;> omega
  simp only [leapSecondOK, Rfc3339.Spec.LeapSecondAllowed, Rfc3339.Spec.utcMinute, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, daysInMonth_eq, offsetMinutes_eq]
  have hN := dayNumber_day y m d
  have hdim := daysInMonth_bounds y m hm1 hm2
  constructor
  · rintro (⟨hu, rfl⟩ | ⟨hu, rfl⟩)
    · rcases Nat.lt_or_ge m 12 with hm | hm
      · refine ⟨y, m + 1, by omega, by omega, ?_⟩
        have := next_month y m hm1
        omega
      · have hm12 : m = 12 := by omega
        subst hm12
        refine ⟨y + 1, 1, by omega, by omega, ?_⟩
        have := next_year y
        have : Rfc3339.Spec.daysInMonth y 12 = 31 := by simp [Rfc3339.Spec.daysInMonth]
        omega
    · exact ⟨y, m, hm1, hm2, by omega⟩
  · rintro ⟨y', m', h1', h2', heq⟩
    have hsp := @month_start_spaced y m y' m' hm1 hm2 h1' h2'
    omega

/-! ## Validity -/

theorem isValid_iff (t : Timestamp) : t.isValid = true ↔ Rfc3339.Spec.Valid t := by
  simp only [Timestamp.isValid, Rfc3339.Spec.Valid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, daysInMonth_eq, all_lt_iff, offset_isValid_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy, hm1⟩, hm2⟩, hd1⟩, hd2⟩, hh⟩, hmi⟩, hs⟩, hleap⟩, hf⟩, ho⟩
    refine ⟨hy, hm1, hm2, hd1, hd2, hh, hmi, hs, ?_, hf, ho⟩
    intro h60
    rcases hleap with h | h
    · exact absurd h60 h
    · exact (leapSecondOK_iff t hm1 hm2 hd1 hd2 hh hmi ho).1 h
  · rintro ⟨hy, hm1, hm2, hd1, hd2, hh, hmi, hs, hleap, hf, ho⟩
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hy, hm1⟩, hm2⟩, hd1⟩, hd2⟩, hh⟩, hmi⟩, hs⟩, ?_⟩, hf⟩, ho⟩
    by_cases h60 : t.second = 60
    · exact Or.inr ((leapSecondOK_iff t hm1 hm2 hd1 hd2 hh hmi ho).2 (hleap h60))
    · exact Or.inl h60

end Rfc3339.Proofs.Valid
