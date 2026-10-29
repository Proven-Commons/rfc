/-
  The leap second table: the code's (year, month) list against the
  spec's NTP times, and `isValidKnown` against `Rfc3339.Spec.ValidKnown`.
-/

import Rfc3339
import Rfc3339.Spec.Leap
import Rfc3339.Proofs.Valid
import Rfc3339.Proofs.Instant
import Rfc3339.Proofs.FromUnix.Day

open Rfc3339

namespace Rfc3339.Proofs.Leap

/-- The leap seconds of the code's list, in order, are those of the
    table's lines after the first. -/
theorem leapKey_table :
    leapMonths.map leapKey = Rfc3339.Spec.leapTable.tail.map (fun e => Rfc3339.Spec.leapSecondKey e.1) := by
  decide +kernel

/-- The day number of the first day of the month after `ym`, as
    `leapKey` computes it. -/
def tb_next (ym : Nat × Nat) : Nat :=
  if ym.2 = 12 then dayNumber (ym.1 + 1) 1 1 else dayNumber ym.1 (ym.2 + 1) 1

theorem tb_leapKey_eq (ym : Nat × Nat) :
    leapKey ym = (((tb_next ym * 1440 : Nat) : Int) - 1) * 61 + 60 := rfl

/-- Each NTP time of the table after the first line is a whole number
    of minutes after the Unix epoch. -/
theorem tb_table_div : ∀ e ∈ Rfc3339.Spec.leapTable.tail, ((e.1 : Int) - Rfc3339.Spec.ntpOfUnix 0) % 60 = 0 := by
  decide +kernel

/-- Facts about each month of the code's list: its range, and that the
    day before the next month starts falls in it. -/
theorem tb_months : ∀ ym ∈ leapMonths, 1972 ≤ ym.1 ∧ ym.1 ≤ 2016 ∧ 1 ≤ ym.2 ∧ ym.2 ≤ 12 ∧
    1 ≤ tb_next ym ∧
    (fromDayNumber (tb_next ym - 1)).1 = ym.1 ∧ (fromDayNumber (tb_next ym - 1)).2.1 = ym.2 := by
  decide +kernel

/-- The month after `(y, m)` starts `daysInMonth y m` days after it. -/
theorem tb_next_eq (y m : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) :
    tb_next (y, m) = Rfc3339.Spec.dayNumber y m 1 + Rfc3339.Spec.daysInMonth y m := by
  unfold tb_next
  simp only
  split
  · rename_i h12
    subst h12
    rw [DayNumber.dayNumber_eq _ _ _ (by decide) (by decide), ← Valid.next_year y]
    simp [Rfc3339.Spec.daysInMonth]
  · rw [DayNumber.dayNumber_eq _ _ _ (by omega) (by omega), Valid.next_month y m hm1]

theorem tb_utcMonth_eq (t : Timestamp) :
    t.utcMonth = ((fromDayNumber (t.utcMinute / 1440).toNat).1,
      (fromDayNumber (t.utcMinute / 1440).toNat).2.1) := rfl

/-- At second 60, a leap second of the code's list is one of the table's. -/
theorem tb_key_iff_table (t : Timestamp) (h : Rfc3339.Spec.Valid t) (h60 : t.second = 60) :
    (∃ ym ∈ leapMonths, leapKey ym = t.utcMinute * 61 + t.second) ↔ Rfc3339.Spec.TableLeapSecond t := by
  have e1 : (∃ ym ∈ leapMonths, leapKey ym = t.utcMinute * 61 + t.second) ↔
      ∃ e ∈ Rfc3339.Spec.leapTable.tail, Rfc3339.Spec.leapSecondKey e.1 = t.utcMinute * 61 + t.second := by
    have := congrArg (fun l => t.utcMinute * 61 + t.second ∈ l) leapKey_table
    simp only [List.mem_map] at this
    exact Iff.of_eq this
  rw [e1, Instant.utcMinute_eq t h]
  unfold Rfc3339.Spec.TableLeapSecond
  simp only [h60, true_and]
  constructor
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    have hd := tb_table_div e he
    unfold Rfc3339.Spec.leapSecondKey at hk
    unfold Rfc3339.Spec.unixSeconds
    rw [Instant.dayNumber_epoch] at hk ⊢
    simp only [Rfc3339.Spec.ntpOfUnix] at hk hd ⊢
    omega
  · rintro ⟨e, he, hk⟩
    refine ⟨e, he, ?_⟩
    unfold Rfc3339.Spec.leapSecondKey
    unfold Rfc3339.Spec.unixSeconds at hk
    rw [Instant.dayNumber_epoch] at hk ⊢
    simp only [Rfc3339.Spec.ntpOfUnix] at hk ⊢
    omega

/-- At a valid second 60, the code's month test is the leap second key test. -/
theorem tb_contains_iff (t : Timestamp) (h : Rfc3339.Spec.Valid t) (h60 : t.second = 60) :
    leapMonths.contains t.utcMonth = true ↔
      ∃ ym ∈ leapMonths, leapKey ym = t.utcMinute * 61 + t.second := by
  obtain ⟨y, m, hm1, hm2, hD⟩ := h.2.2.2.2.2.2.2.2.1 h60
  rw [← Instant.utcMinute_eq t h] at hD
  have hkey : ∀ ym, leapKey ym = t.utcMinute * 61 + t.second ↔
      tb_next ym = Rfc3339.Spec.dayNumber y m 1 := by
    intro ym
    rw [tb_leapKey_eq, h60]
    omega
  simp only [hkey, List.contains_iff_mem]
  rw [tb_utcMonth_eq]
  constructor
  · intro hmem
    have hp := tb_months _ hmem
    generalize hn : (t.utcMinute / 1440).toNat = n at hmem hp
    have hy := FromUnix.yearOfDay_spec n
    have hy1 : (fromDayNumber n).1 = yearOfDay n := rfl
    obtain ⟨hp1, hp2, -, -, -, -, -⟩ := hp
    simp only at hp1 hp2
    rw [hy1] at hp1 hp2
    have h10 : n < daysBeforeYear 10000 := by
      have := FromUnix.dy_mono (show yearOfDay n + 1 ≤ 10000 by omega)
      omega
    have h72 : daysBeforeYear 1972 ≤ n := by
      have := FromUnix.dy_mono hp1
      omega
    have h72' : 0 < daysBeforeYear 1972 := by decide
    have hnD : n + 1 = Rfc3339.Spec.dayNumber y m 1 := by omega
    obtain ⟨-, hm1', hm2', hd1', hd2', hdn⟩ := FromUnix.fromDayNumber_spec n h10
    refine ⟨_, hmem, ?_⟩
    rw [tb_next_eq _ _ hm1' hm2']
    have hday := Valid.dayNumber_day (fromDayNumber n).1 (fromDayNumber n).2.1
      (fromDayNumber n).2.2
    have hsp := Valid.month_start_spaced hm1' hm2' hm1 hm2 (show
      Rfc3339.Spec.dayNumber (fromDayNumber n).1 (fromDayNumber n).2.1 1 < Rfc3339.Spec.dayNumber y m 1 by omega)
    omega
  · rintro ⟨ym, hmem, hk⟩
    obtain ⟨-, -, -, -, hn1, hy, hm⟩ := tb_months ym hmem
    have hn : (t.utcMinute / 1440).toNat = tb_next ym - 1 := by omega
    rw [hn, hy, hm]
    exact hmem

theorem isValidKnown_iff (t : Timestamp) : t.isValidKnown = true ↔ Rfc3339.Spec.ValidKnown t := by
  unfold Timestamp.isValidKnown Rfc3339.Spec.ValidKnown
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Valid.isValid_iff]
  constructor
  · rintro ⟨hv, hl⟩
    refine ⟨hv, fun h60 => ?_⟩
    rcases hl with hl | hl
    · exact absurd h60 hl
    · exact (tb_key_iff_table t hv h60).1 ((tb_contains_iff t hv h60).1 hl)
  · rintro ⟨hv, hl⟩
    refine ⟨hv, ?_⟩
    by_cases h60 : t.second = 60
    · exact Or.inr ((tb_contains_iff t hv h60).2 ((tb_key_iff_table t hv h60).2 (hl h60)))
    · exact Or.inl h60

/-- A known-valid second 60 sits at one of the list's leap seconds. -/
theorem leapKey_of_known (t : Timestamp) (h : Rfc3339.Spec.ValidKnown t) (h60 : t.second = 60) :
    ∃ ym ∈ leapMonths, leapKey ym = t.utcMinute * 61 + t.second :=
  (tb_key_iff_table t h.1 h60).2 (h.2 h60)

/-- And a valid second 60 at one of the list's leap seconds is known
    valid. -/
theorem known_of_leapKey (t : Timestamp) (h : Rfc3339.Spec.Valid t) (ym : Nat × Nat)
    (hym : ym ∈ leapMonths) (hk : leapKey ym = t.utcMinute * 61 + t.second) :
    Rfc3339.Spec.ValidKnown t :=
  ⟨h, fun h60 => (tb_key_iff_table t h h60).1 ⟨ym, hym, hk⟩⟩

end Rfc3339.Proofs.Leap
