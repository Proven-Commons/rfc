/-
  `fromUnixSeconds` against the spec, from the lemmas in `Day.lean` and
  the first slice's proofs of `unixSeconds` and the day number.
-/

import Rfc3339
import Spec.Defs
import Proofs.DayNumber
import Proofs.Instant
import Proofs.FromUnix.Day

namespace Rfc3339.Proofs.FromUnix

open Rfc3339

/-- `daysBeforeYear 10000`: the days before 10000-01-01. -/
theorem fu_daysBeforeYear_10000 : daysBeforeYear 10000 = 3652425 := by decide

/-- A UTC timestamp's Unix seconds, shifted to count from 0000-01-01:
    its day number in seconds, plus the time of day. -/
theorem fu_unixSeconds_z (t : Timestamp) (hz : t.offset = .z) :
    Spec.unixSeconds t + 719528 * 86400 =
      ((Spec.dayNumber t.year t.month t.day * 86400 + t.hour * 3600 + t.minute * 60 +
        t.second : Nat) : Int) := by
  unfold Spec.unixSeconds Spec.utcMinute
  rw [hz, Instant.dayNumber_epoch]
  simp only [Spec.offsetMinutes]
  omega

/-- The first second of the range. -/
theorem fu_unixSeconds_lo : Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ = -62167219200 := by
  decide +kernel

/-- The last second of the range. -/
theorem fu_unixSeconds_hi :
    Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 253402300799 := by
  decide +kernel

end Rfc3339.Proofs.FromUnix

open Rfc3339

theorem Spec.fromUnixSeconds_iff (s : Int) (t : Timestamp) :
    Rfc3339.fromUnixSeconds s = some t ↔
      Spec.Valid t ∧ t.offset = .z ∧ t.fraction = [] ∧ t.second ≤ 59 ∧
        Spec.unixSeconds t = s := by
  have hD := Proofs.FromUnix.fu_daysBeforeYear_10000
  constructor
  · intro h
    unfold Rfc3339.fromUnixSeconds at h
    dsimp only at h
    split at h
    · rename_i hr
      have hn : (s + 719528 * 86400).toNat / 86400 < daysBeforeYear 10000 := by omega
      have hs := Proofs.FromUnix.fromDayNumber_spec _ hn
      generalize fromDayNumber ((s + 719528 * 86400).toNat / 86400) = p at h hs
      obtain ⟨y, m, d⟩ := p
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
      have hu := Proofs.FromUnix.fu_unixSeconds_z
        ⟨y, m, d, (s + 719528 * 86400).toNat % 86400 / 3600,
          (s + 719528 * 86400).toNat % 86400 % 3600 / 60, (s + 719528 * 86400).toNat % 86400 % 60,
          [], .z⟩ rfl
      simp only at h1 h2 h3 h4 h5 h6 hu
      rw [h6] at hu
      refine ⟨⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
      · show _ / 3600 ≤ 23; omega
      · show _ % 3600 / 60 ≤ 59; omega
      · show _ % 60 ≤ 60; omega
      · intro h60; exfalso; change _ % 60 = 60 at h60; omega
      · intro x hx; cases hx
      · trivial
      · show _ % 60 ≤ 59; omega
      · omega
    · contradiction
  · rintro ⟨hv, hz, hf, hs59, hu⟩
    obtain ⟨y, m, d, hh, mi, sec, fr, off⟩ := t
    simp only at hz hf hs59 hu
    subst hz hf
    obtain ⟨hy, hm1, hm2, hd1, hd2, hh23, hmi, -, -, -, -⟩ := hv
    have hu' := Proofs.FromUnix.fu_unixSeconds_z ⟨y, m, d, hh, mi, sec, [], .z⟩ rfl
    simp only at hu' hy hm1 hm2 hd1 hd2 hh23 hmi
    rw [hu] at hu'
    have hN := Proofs.FromUnix.dayNumber_lt y m d hy ⟨hm1, hm2⟩ ⟨hd1, hd2⟩
    unfold Rfc3339.fromUnixSeconds
    dsimp only
    split
    case isFalse hr => exfalso; omega
    have hn : (s + 719528 * 86400).toNat / 86400 = Spec.dayNumber y m d := by omega
    have hsec : (s + 719528 * 86400).toNat % 86400 = hh * 3600 + mi * 60 + sec := by omega
    rw [hn, hsec]
    have hs := Proofs.FromUnix.fromDayNumber_spec _ hN
    generalize fromDayNumber (Spec.dayNumber y m d) = p at hs ⊢
    obtain ⟨y', m', d'⟩ := p
    obtain ⟨-, h2, h3, h4, h5, h6⟩ := hs
    simp only at h2 h3 h4 h5 h6
    obtain ⟨rfl, rfl, rfl⟩ :=
      Proofs.FromUnix.dayNumber_inj y' m' d' y m d ⟨h2, h3⟩ ⟨h4, h5⟩ ⟨hm1, hm2⟩ ⟨hd1, hd2⟩ h6
    simp only [Option.some.injEq, Timestamp.mk.injEq, true_and, and_true]
    and_intros <;> omega

theorem Spec.fromUnixSeconds_isSome (s : Int) :
    (Rfc3339.fromUnixSeconds s).isSome ↔
      Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ≤ s ∧
        s ≤ Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := by
  rw [Proofs.FromUnix.fu_unixSeconds_lo, Proofs.FromUnix.fu_unixSeconds_hi]
  have hD := Proofs.FromUnix.fu_daysBeforeYear_10000
  unfold Rfc3339.fromUnixSeconds
  dsimp only
  split
  · rename_i hr
    generalize fromDayNumber ((s + 719528 * 86400).toNat / 86400) = p
    obtain ⟨y, m, d⟩ := p
    simp only [Option.isSome_some, true_iff]
    omega
  · rename_i hr
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    omega

theorem Spec.fromUnixSeconds_vectors :
    Rfc3339.fromUnixSeconds 0 = some ⟨1970, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 482196050 = some ⟨1985, 4, 12, 23, 20, 50, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 951782400 = some ⟨2000, 2, 29, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 2147483647 = some ⟨2038, 1, 19, 3, 14, 7, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-1) = some ⟨1969, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Spec.unixSeconds ⟨0, 1, 1, 0, 0, 0, [], .z⟩ = -62167219200 ∧
    Spec.unixSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 253402300799 ∧
    Rfc3339.fromUnixSeconds (-62167219200) = some ⟨0, 1, 1, 0, 0, 0, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds 253402300799 = some ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ ∧
    Rfc3339.fromUnixSeconds (-62167219201) = none ∧
    Rfc3339.fromUnixSeconds 253402300800 = none := by
  and_intros <;> decide +kernel
