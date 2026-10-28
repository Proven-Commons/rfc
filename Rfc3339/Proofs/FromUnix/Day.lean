/-
  From a day number back to a date: `yearOfDay`, `monthOfDay` and
  `fromDayNumber`, and that a valid date's day number determines it.
-/

import Rfc3339
import Rfc3339.Spec.Defs
import Rfc3339.Proofs.DayNumber

namespace Rfc3339.Proofs.FromUnix

open Rfc3339

/-! ### Years -/

/-- `daysBeforeYear y` stays within a couple of days of `146097 * y / 400`. -/
theorem dy_bound (y : Nat) :
    146097 * y ≤ 400 * daysBeforeYear y + 396 ∧ 400 * daysBeforeYear y ≤ 146097 * y + 699 := by
  unfold daysBeforeYear; omega

/-- `daysBeforeYear` is strictly increasing. -/
theorem dy_strict {a b : Nat} (h : a < b) : daysBeforeYear a < daysBeforeYear b := by
  have := dy_bound a; have := dy_bound b; omega

/-- `daysBeforeYear` is monotone. -/
theorem dy_mono {a b : Nat} (h : a ≤ b) : daysBeforeYear a ≤ daysBeforeYear b := by
  rcases Nat.eq_or_lt_of_le h with h | h
  · subst h; exact Nat.le_refl _
  · exact Nat.le_of_lt (dy_strict h)

/-- The year `yearOfDay` gives is the one day `n` falls in. -/
theorem yearOfDay_spec (n : Nat) :
    daysBeforeYear (yearOfDay n) ≤ n ∧ n < daysBeforeYear (yearOfDay n + 1) := by
  unfold yearOfDay
  generalize he : n * 400 / 146097 = e
  have h1 : 146097 * e ≤ 400 * n := by omega
  have h2 : 400 * n < 146097 * (e + 1) := by omega
  simp only
  split
  · have := dy_bound (e + 1 + 1)
    omega
  · split
    · cases e with
      | zero => simp [daysBeforeYear] at *
      | succ k =>
        have := dy_bound k
        simp only [Nat.add_sub_cancel]
        omega
    · omega

/-- The length of year `y`, from the code's leap year rule. -/
theorem dy_yearLength (y : Nat) : Rfc3339.Spec.yearLength y = if isLeapYear y then 366 else 365 := by
  unfold Rfc3339.Spec.yearLength; rw [DayNumber.isLeapYear_eq]

/-! ### Months -/

theorem dy_dbm_congr {y y' : Nat} (m : Nat) (h : isLeapYear y = isLeapYear y') :
    daysBeforeMonth y m = daysBeforeMonth y' m := by
  unfold daysBeforeMonth; rw [h]

theorem dy_dim_congr {y y' : Nat} (m : Nat) (h : isLeapYear y = isLeapYear y') :
    daysInMonth y m = daysInMonth y' m := by
  simp only [daysInMonth, h]

theorem dy_mod_congr {y y' : Nat} (doy : Nat) (h : isLeapYear y = isLeapYear y') :
    monthOfDay y doy = monthOfDay y' doy := by
  unfold monthOfDay; simp only [dy_dbm_congr _ h]

/-- Year 0 is a leap year and year 1 is not; the tables below are for those two. -/
theorem dy_table_leap : ∀ doy, doy < 366 →
    1 ≤ monthOfDay 0 doy ∧ monthOfDay 0 doy ≤ 12 ∧
    daysBeforeMonth 0 (monthOfDay 0 doy) ≤ doy ∧
    doy < daysBeforeMonth 0 (monthOfDay 0 doy) + daysInMonth 0 (monthOfDay 0 doy) := by
  decide +kernel

theorem dy_table_common : ∀ doy, doy < 365 →
    1 ≤ monthOfDay 1 doy ∧ monthOfDay 1 doy ≤ 12 ∧
    daysBeforeMonth 1 (monthOfDay 1 doy) ≤ doy ∧
    doy < daysBeforeMonth 1 (monthOfDay 1 doy) + daysInMonth 1 (monthOfDay 1 doy) := by
  decide +kernel

theorem dy_uniq_leap : ∀ m, m < 13 → 1 ≤ m → ∀ k, k < daysInMonth 0 m →
    monthOfDay 0 (daysBeforeMonth 0 m + k) = m := by
  decide +kernel

theorem dy_uniq_common : ∀ m, m < 13 → 1 ≤ m → ∀ k, k < daysInMonth 1 m →
    monthOfDay 1 (daysBeforeMonth 1 m + k) = m := by
  decide +kernel

theorem dy_end_leap : ∀ m, m < 13 → 1 ≤ m → daysBeforeMonth 0 m + daysInMonth 0 m ≤ 366 := by
  decide +kernel

theorem dy_end_common : ∀ m, m < 13 → 1 ≤ m → daysBeforeMonth 1 m + daysInMonth 1 m ≤ 365 := by
  decide +kernel

/-- `monthOfDay` gives the month that day `doy` of year `y` falls in. -/
theorem dy_month (y doy : Nat) (h : doy < Rfc3339.Spec.yearLength y) :
    1 ≤ monthOfDay y doy ∧ monthOfDay y doy ≤ 12 ∧
    daysBeforeMonth y (monthOfDay y doy) ≤ doy ∧
    doy < daysBeforeMonth y (monthOfDay y doy) + daysInMonth y (monthOfDay y doy) := by
  rw [dy_yearLength] at h
  cases hl : isLeapYear y
  · have e : isLeapYear y = isLeapYear 1 := by rw [hl]; rfl
    rw [dy_mod_congr doy e, dy_dbm_congr _ e, dy_dim_congr _ e]
    simp only [hl, Bool.false_eq_true, ite_false] at h
    exact dy_table_common doy h
  · have e : isLeapYear y = isLeapYear 0 := by rw [hl]; rfl
    rw [dy_mod_congr doy e, dy_dbm_congr _ e, dy_dim_congr _ e]
    simp only [hl, ite_true] at h
    exact dy_table_leap doy h

/-- A day within month `m` of year `y` falls in month `m`. -/
theorem dy_month_uniq (y m k : Nat) (hm : 1 ≤ m ∧ m ≤ 12) (hk : k < daysInMonth y m) :
    monthOfDay y (daysBeforeMonth y m + k) = m := by
  cases hl : isLeapYear y
  · have e : isLeapYear y = isLeapYear 1 := by rw [hl]; rfl
    rw [dy_mod_congr _ e, dy_dbm_congr _ e]
    rw [dy_dim_congr _ e] at hk
    exact dy_uniq_common m (by omega) hm.1 k hk
  · have e : isLeapYear y = isLeapYear 0 := by rw [hl]; rfl
    rw [dy_mod_congr _ e, dy_dbm_congr _ e]
    rw [dy_dim_congr _ e] at hk
    exact dy_uniq_leap m (by omega) hm.1 k hk

/-- A month ends within its year. -/
theorem dy_month_end (y m : Nat) (hm : 1 ≤ m ∧ m ≤ 12) :
    daysBeforeMonth y m + daysInMonth y m ≤ Rfc3339.Spec.yearLength y := by
  rw [dy_yearLength]
  cases hl : isLeapYear y
  · have e : isLeapYear y = isLeapYear 1 := by rw [hl]; rfl
    rw [dy_dbm_congr _ e, dy_dim_congr _ e]
    exact dy_end_common m (by omega) hm.1
  · have e : isLeapYear y = isLeapYear 0 := by rw [hl]; rfl
    rw [dy_dbm_congr _ e, dy_dim_congr _ e]
    exact dy_end_leap m (by omega) hm.1

/-! ### Dates -/

/-- `fromDayNumber` gives a valid date with day number `n`, in a year no
    later than 9999 when `n` is before 10000-01-01. -/
theorem fromDayNumber_spec (n : Nat) (h : n < daysBeforeYear 10000) :
    (fromDayNumber n).1 ≤ 9999 ∧
    1 ≤ (fromDayNumber n).2.1 ∧ (fromDayNumber n).2.1 ≤ 12 ∧
    1 ≤ (fromDayNumber n).2.2 ∧
    (fromDayNumber n).2.2 ≤ Rfc3339.Spec.daysInMonth (fromDayNumber n).1 (fromDayNumber n).2.1 ∧
    Rfc3339.Spec.dayNumber (fromDayNumber n).1 (fromDayNumber n).2.1 (fromDayNumber n).2.2 = n := by
  obtain ⟨h1, h2⟩ := yearOfDay_spec n
  have hy : yearOfDay n ≤ 9999 := by
    apply Nat.le_of_not_lt
    intro c
    have := dy_mono (show 10000 ≤ yearOfDay n by omega)
    omega
  have hdoy : n - daysBeforeYear (yearOfDay n) < Rfc3339.Spec.yearLength (yearOfDay n) := by
    rw [DayNumber.daysBeforeYear_succ] at h2; omega
  obtain ⟨hm1, hm2, hm3, hm4⟩ := dy_month _ _ hdoy
  simp only [fromDayNumber]
  refine ⟨hy, hm1, hm2, by omega, ?_, ?_⟩
  · rw [← DayNumber.daysInMonth_eq]; omega
  · rw [← DayNumber.dayNumber_eq _ _ _ hm1 hm2]; unfold dayNumber; omega

/-- A valid date's day number lies in its year. -/
theorem dy_dayNumber_bounds (y m d : Nat) (hm : 1 ≤ m ∧ m ≤ 12)
    (hd : 1 ≤ d ∧ d ≤ Rfc3339.Spec.daysInMonth y m) :
    daysBeforeYear y ≤ Rfc3339.Spec.dayNumber y m d ∧ Rfc3339.Spec.dayNumber y m d < daysBeforeYear (y + 1) := by
  rw [← DayNumber.dayNumber_eq _ _ _ hm.1 hm.2, DayNumber.daysBeforeYear_succ]
  rw [← DayNumber.daysInMonth_eq] at hd
  have := dy_month_end y m hm
  unfold dayNumber
  omega

/-- Two valid dates with the same day number are the same date. -/
theorem dayNumber_inj (y m d y' m' d' : Nat)
    (hm : 1 ≤ m ∧ m ≤ 12) (hd : 1 ≤ d ∧ d ≤ Rfc3339.Spec.daysInMonth y m)
    (hm' : 1 ≤ m' ∧ m' ≤ 12) (hd' : 1 ≤ d' ∧ d' ≤ Rfc3339.Spec.daysInMonth y' m')
    (h : Rfc3339.Spec.dayNumber y m d = Rfc3339.Spec.dayNumber y' m' d') : y = y' ∧ m = m' ∧ d = d' := by
  have b := dy_dayNumber_bounds y m d hm hd
  have b' := dy_dayNumber_bounds y' m' d' hm' hd'
  have hy : y = y' := by
    rcases Nat.lt_trichotomy y y' with c | c | c
    · have := dy_mono (show y + 1 ≤ y' by omega); omega
    · exact c
    · have := dy_mono (show y' + 1 ≤ y by omega); omega
  subst hy
  rw [← DayNumber.dayNumber_eq _ _ _ hm.1 hm.2, ← DayNumber.dayNumber_eq _ _ _ hm'.1 hm'.2] at h
  unfold dayNumber at h
  rw [← DayNumber.daysInMonth_eq] at hd hd'
  have u := dy_month_uniq y m (d - 1) hm (by omega)
  have u' := dy_month_uniq y m' (d' - 1) hm' (by omega)
  have e : daysBeforeMonth y m + (d - 1) = daysBeforeMonth y m' + (d' - 1) := by omega
  have hmm : m = m' := by
    calc m = monthOfDay y (daysBeforeMonth y m + (d - 1)) := u.symm
      _ = monthOfDay y (daysBeforeMonth y m' + (d' - 1)) := by rw [e]
      _ = m' := u'
  subst hmm
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- A valid date in a year no later than 9999 falls before 10000-01-01. -/
theorem dayNumber_lt (y m d : Nat) (hy : y ≤ 9999) (hm : 1 ≤ m ∧ m ≤ 12)
    (hd : 1 ≤ d ∧ d ≤ Rfc3339.Spec.daysInMonth y m) : Rfc3339.Spec.dayNumber y m d < daysBeforeYear 10000 := by
  have b := dy_dayNumber_bounds y m d hm hd
  have := dy_mono (show y + 1 ≤ 10000 by omega)
  omega

end Rfc3339.Proofs.FromUnix
