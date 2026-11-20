/-
  From SI seconds back to a timestamp.
-/

import Rfc3339.Proofs.Leap.Si
import Rfc3339.Proofs.Leap.Order
import Rfc3339.Proofs.FromUnix.Main

open Rfc3339

namespace Rfc3339.Proofs.Leap

/-! ## Counting a prefix -/

/-- A predicate closed downward on `0, …, N - 1` holds exactly below
    the number of indices it holds for. -/
theorem fs_count_prefix (p : Nat → Bool) : ∀ N : Nat,
    (∀ i j, i ≤ j → j < N → p j = true → p i = true) →
    ((List.range N).filter p).length ≤ N ∧
      ∀ i, i < N → (p i = true ↔ i < ((List.range N).filter p).length)
  | 0, _ => by simp
  | N + 1, hm => by
    have ih := fs_count_prefix p N (fun i j hij hj hp => hm i j hij (by omega) hp)
    rw [List.range_succ, List.filter_append, List.length_append]
    cases hpN : p N with
    | true =>
      have hall : ∀ i, i < N + 1 → p i = true := fun i hi => hm i N (by omega) (by omega) hpN
      have hk : ((List.range N).filter p).length = N := by
        rcases Nat.eq_zero_or_pos N with h0 | hpos
        · subst h0; simp
        · have := (ih.2 (N - 1) (by omega)).mp (hall _ (by omega)); omega
      simp only [List.filter_cons, hpN, List.filter_nil, ite_true, List.length_singleton, hk]
      refine ⟨by omega, fun i hi => ?_⟩
      simp only [hall i hi, true_iff]; omega
    | false =>
      simp only [List.filter_cons, hpN, List.filter_nil, Bool.false_eq_true, ite_false,
        List.length_nil, Nat.add_zero]
      refine ⟨by omega, fun i hi => ?_⟩
      rcases Nat.lt_or_ge i N with h | h
      · exact ih.2 i h
      · have : i = N := by omega
        subst this
        simp only [hpN, Bool.false_eq_true, false_iff]
        omega

/-- The number of indices below `N` that satisfy `p`, when `p` holds
    exactly below `k`. -/
theorem fs_count_lt (p : Nat → Bool) (N k : Nat) (hk : k ≤ N)
    (h : ∀ i, i < N → (p i = true ↔ i < k)) : ((List.range N).filter p).length = k := by
  have hc := fs_count_prefix p N (fun i j hij hj hp => (h i (by omega)).mpr
    (by have := (h j hj).mp hp; omega))
  rcases Nat.lt_trichotomy ((List.range N).filter p).length k with c | c | c
  · exfalso
    have h1 := (h _ (by omega)).mpr c
    have h2 := (hc.2 _ (by omega)).mp h1
    omega
  · exact c
  · exfalso
    have h1 := (hc.2 k (by omega)).mpr c
    have h2 := (h k (by omega)).mp h1
    omega

/-! ## The list, by index -/

/-- The `i`-th month of the list. -/
def fs_ym (i : Nat) : Nat × Nat := leapMonths.getD i (0, 0)

/-- The Unix seconds of the instant just after the `i`-th leap second,
    less those of 1972-01-01T00:00:00Z. -/
def fs_V (i : Nat) : Int := (leapKey (fs_ym i) + 1) / 61 * 60 - 719528 * 86400 - 63072000

theorem fs_leapMonths_eq : leapMonths = (List.range 27).map fs_ym := by decide +kernel

theorem fs_leapSiSeconds_eq : leapSiSeconds = (List.range 27).map (fun i => fs_V i + i) := by
  decide +kernel

theorem fs_V_mono_dec : ∀ j, j < 27 → ∀ i, i < j → fs_V i < fs_V j := by decide +kernel

theorem fs_V_mono (i j : Nat) (hij : i ≤ j) (hj : j < 27) : fs_V i ≤ fs_V j := by
  rcases Nat.lt_or_ge i j with h | h
  · exact Int.le_of_lt (fs_V_mono_dec j hj i h)
  · have : i = j := by omega
    subst this; exact Int.le_refl _

theorem fs_key_mod : ∀ i, i < 27 → (leapKey (fs_ym i) + 1) % 87840 = 0 := by decide +kernel

theorem fs_V_zero : fs_V 0 = 15724800 := by decide +kernel

theorem fs_V_last : fs_V 26 = 1420156800 := by decide +kernel

theorem fs_mem_leapSiSeconds (n : Int) : n ∈ leapSiSeconds ↔ ∃ i, i < 27 ∧ fs_V i + i = n := by
  rw [fs_leapSiSeconds_eq, List.mem_map]
  simp only [List.mem_range]

/-- The count `fromSiSeconds` makes. -/
theorem fs_k_eq (n : Int) : (leapSiSeconds.filter (· < n)).length =
    ((List.range 27).filter (fun i => decide (fs_V i + i < n))).length := by
  rw [fs_leapSiSeconds_eq, List.filter_map, List.length_map]
  rfl

theorem fs_k_char (n : Int) :
    (leapSiSeconds.filter (· < n)).length ≤ 27 ∧
      ∀ i, i < 27 → (fs_V i + i < n ↔ i < (leapSiSeconds.filter (· < n)).length) := by
  rw [fs_k_eq]
  have hc := fs_count_prefix (fun i => decide (fs_V i + i < n)) 27 (by
    intro i j hij hj hp
    simp only [decide_eq_true_eq] at hp ⊢
    have := fs_V_mono i j hij hj
    omega)
  refine ⟨hc.1, fun i hi => ?_⟩
  have := hc.2 i hi
  simp only [decide_eq_true_eq] at this
  exact this

/-- Off the leap seconds, the `i`-th leap second comes before `n - k`
    Unix seconds after 1972 exactly when it is one of the `k` below `n`. -/
theorem fs_V_le_iff (n : Int) (hn : n ∉ leapSiSeconds) (i : Nat) (hi : i < 27) :
    fs_V i ≤ n - (leapSiSeconds.filter (· < n)).length ↔
      i < (leapSiSeconds.filter (· < n)).length := by
  obtain ⟨hk, hc⟩ := fs_k_char n
  have hne : ∀ j, j < 27 → fs_V j + j ≠ n := fun j hj e =>
    hn ((fs_mem_leapSiSeconds n).mpr ⟨j, hj, e⟩)
  generalize (leapSiSeconds.filter (· < n)).length = k at hk hc ⊢
  constructor
  · intro h
    apply Nat.lt_of_not_le
    intro hik
    have hk27 : k < 27 := by omega
    have h1 : ¬ fs_V k + k < n := fun c => by have := (hc k hk27).mp c; omega
    have h2 := hne k hk27
    have h3 := fs_V_mono k i hik hi
    omega
  · intro h
    have h1 := (hc (k - 1) (by omega)).mpr (by omega)
    have h2 := fs_V_mono i (k - 1) (by omega) (by omega)
    omega

/-! ## Leap seconds before a second other than 60 -/

theorem fs_unix_utc (t : Timestamp) :
    t.unixSeconds = (t.utcMinute - 719528 * 1440) * 60 + t.second := by
  unfold Timestamp.unixSeconds Timestamp.utcMinute
  omega

theorem fs_lt_key_iff (t : Timestamp) (h59 : t.second ≤ 59) (i : Nat) (hi : i < 27) :
    leapKey (fs_ym i) < t.utcMinute * 61 + t.second ↔ fs_V i + 63072000 ≤ t.unixSeconds := by
  have := fs_key_mod i hi
  rw [fs_unix_utc]
  unfold fs_V
  omega

theorem fs_leapsBefore_of_le59 (t : Timestamp) (h59 : t.second ≤ 59) :
    t.leapsBefore =
      ((List.range 27).filter (fun i => decide (fs_V i + 63072000 ≤ t.unixSeconds))).length := by
  unfold Timestamp.leapsBefore
  rw [fs_leapMonths_eq, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  exact decide_eq_decide.mpr (fs_lt_key_iff t h59 i hi)


/-! ## The leap seconds themselves -/

/-- What `fromSiSeconds n` gives, checked: a UTC timestamp with no
    fraction, known valid, from 1972 on, with SI seconds `n`. -/
def fs_check (n : Int) : Bool :=
  match fromSiSeconds n with
  | some t => decide (t.offset = .z) && decide (t.fraction = []) && t.isValidKnown &&
      decide (1972 ≤ t.year) && decide (t.siSeconds = n)
  | none => false

theorem fs_check_leap : ∀ n ∈ leapSiSeconds, fs_check n = true := by decide +kernel

/-! ## Bounds -/

theorem fs_unix_1972 : Rfc3339.Spec.unixSeconds ⟨1972, 1, 1, 0, 0, 0, [], .z⟩ = 63072000 := by
  decide +kernel

theorem fs_dby_1972 : daysBeforeYear 1972 = 720258 := by decide

theorem fs_si_max : Rfc3339.Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 253339228826 := by
  decide +kernel

/-- A valid UTC second other than 60, at or after 1972-01-01T00:00:00Z,
    is in 1972 or later. -/
theorem fs_year_of_unix (t : Timestamp) (hv : Rfc3339.Spec.Valid t) (hz : t.offset = .z)
    (h59 : t.second ≤ 59) (hu : 63072000 ≤ Rfc3339.Spec.unixSeconds t) : 1972 ≤ t.year := by
  apply Nat.le_of_not_lt
  intro hy
  obtain ⟨_, hm1, hm2, hd1, hd2, hh, hmi, _⟩ := hv
  have e := FromUnix.fu_unixSeconds_z t hz
  have b := FromUnix.dy_dayNumber_bounds t.year t.month t.day ⟨hm1, hm2⟩ ⟨hd1, hd2⟩
  have m := FromUnix.dy_mono (show t.year + 1 ≤ 1972 by omega)
  rw [fs_dby_1972] at m
  omega

/-- A valid UTC timestamp in 1972 or later is at or after
    1972-01-01T00:00:00Z. -/
theorem fs_unix_of_year (t : Timestamp) (hv : Rfc3339.Spec.Valid t) (hz : t.offset = .z)
    (hy : 1972 ≤ t.year) : 63072000 ≤ Rfc3339.Spec.unixSeconds t := by
  obtain ⟨_, hm1, hm2, hd1, hd2, _⟩ := hv
  have e := FromUnix.fu_unixSeconds_z t hz
  have b := FromUnix.dy_dayNumber_bounds t.year t.month t.day ⟨hm1, hm2⟩ ⟨hd1, hd2⟩
  have m := FromUnix.dy_mono hy
  rw [fs_dby_1972] at m
  omega

theorem fs_si_nonneg (t : Timestamp) (hv : Rfc3339.Spec.Valid t) (hz : t.offset = .z)
    (hy : 1972 ≤ t.year) : 0 ≤ Rfc3339.Spec.siSeconds t := by
  unfold Rfc3339.Spec.siSeconds
  rw [fs_unix_1972]
  have := fs_unix_of_year t hv hz hy
  omega

theorem fs_Tmax_known : Rfc3339.Spec.ValidKnown ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ :=
  (isValidKnown_iff _).mp (by decide +kernel)

theorem fs_Tmax_utcMinute :
    Timestamp.utcMinute ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ = 5259491999 := by decide +kernel

theorem fs_leapKey_lt_max : ∀ ym ∈ leapMonths, leapKey ym < 5259491999 * 61 + 59 := by
  decide +kernel

theorem fs_key_le_max (t : Timestamp) (hk : Rfc3339.Spec.ValidKnown t) (hz : t.offset = .z) :
    t.utcMinute * 61 + t.second ≤ 5259491999 * 61 + 59 := by
  obtain ⟨hy, hm1, hm2, hd1, hd2, hh, hmi, hs, _⟩ := hk.1
  by_cases h60 : t.second = 60
  · obtain ⟨ym, hym, e⟩ := leapKey_of_known t hk h60
    have := fs_leapKey_lt_max ym hym
    omega
  · have hN := FromUnix.dayNumber_lt t.year t.month t.day hy ⟨hm1, hm2⟩ ⟨hd1, hd2⟩
    rw [FromUnix.fu_daysBeforeYear_10000, ← DayNumber.dayNumber_eq _ _ _ hm1 hm2] at hN
    unfold Timestamp.utcMinute
    rw [hz]
    simp only [offsetMinutes]
    omega

/-- A known-valid UTC whole second is no later than
    9999-12-31T23:59:59Z, in SI seconds. -/
theorem fs_si_le_max (t : Timestamp) (hk : Rfc3339.Spec.ValidKnown t) (hz : t.offset = .z)
    (hf : t.fraction = []) :
    Rfc3339.Spec.siSeconds t ≤ Rfc3339.Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := by
  have ho := siSeconds_order t _ hk fs_Tmax_known hf rfl
  rw [siSeconds_eq t hk.1, siSeconds_eq _ fs_Tmax_known.1] at ho
  have hkey : t.utcMinute * 61 + (t.second : Int) ≤
      Timestamp.utcMinute ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ * 61 +
        ((Timestamp.second ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ : Nat) : Int) := by
    rw [fs_Tmax_utcMinute]
    exact fs_key_le_max t hk hz
  apply Int.not_lt.mp
  intro c
  rw [Int.compare_eq_gt.mpr c] at ho
  unfold Timestamp.compareInstant at ho
  rcases Int.lt_or_eq_of_le hkey with h | h
  · rw [Int.compare_eq_lt.mpr h] at ho
    cases ho
  · rw [Int.compare_eq_eq.mpr h, hf] at ho
    simp [compareFraction] at ho

/-! ## Uniqueness -/

theorem fs_eq_of_key (t t' : Timestamp) (hv : Rfc3339.Spec.Valid t) (hv' : Rfc3339.Spec.Valid t')
    (hz : t.offset = .z) (hz' : t'.offset = .z) (hf : t.fraction = []) (hf' : t'.fraction = [])
    (h : t.utcMinute * 61 + t.second = t'.utcMinute * 61 + t'.second) : t = t' := by
  obtain ⟨y, m, d, hh, mi, s, fr, off⟩ := t
  obtain ⟨y', m', d', hh', mi', s', fr', off'⟩ := t'
  simp only at hz hz' hf hf'
  subst hz hz' hf hf'
  obtain ⟨_, hm1, hm2, hd1, hd2, hh23, hmi, hs, _⟩ := hv
  obtain ⟨_, hm1', hm2', hd1', hd2', hh23', hmi', hs', _⟩ := hv'
  simp only at hm1 hm2 hd1 hd2 hh23 hmi hs hm1' hm2' hd1' hd2' hh23' hmi' hs'
  unfold Timestamp.utcMinute at h
  simp only [offsetMinutes] at h
  rw [DayNumber.dayNumber_eq _ _ _ hm1 hm2, DayNumber.dayNumber_eq _ _ _ hm1' hm2'] at h
  have hdn : Rfc3339.Spec.dayNumber y m d = Rfc3339.Spec.dayNumber y' m' d' := by omega
  obtain ⟨rfl, rfl, rfl⟩ := FromUnix.dayNumber_inj y m d y' m' d' ⟨hm1, hm2⟩ ⟨hd1, hd2⟩
    ⟨hm1', hm2'⟩ ⟨hd1', hd2'⟩ hdn
  have : hh = hh' ∧ mi = mi' ∧ s = s' := by omega
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

theorem fs_eq_of_si (t t' : Timestamp) (hk : Rfc3339.Spec.ValidKnown t) (hk' : Rfc3339.Spec.ValidKnown t')
    (hz : t.offset = .z) (hz' : t'.offset = .z) (hf : t.fraction = []) (hf' : t'.fraction = [])
    (h : Rfc3339.Spec.siSeconds t = Rfc3339.Spec.siSeconds t') : t = t' := by
  have ho := siSeconds_order t t' hk hk' hf hf'
  rw [siSeconds_eq t hk.1, siSeconds_eq t' hk'.1, h, Int.compare_eq_eq.mpr rfl] at ho
  apply fs_eq_of_key t t' hk.1 hk'.1 hz hz' hf hf'
  unfold Timestamp.compareInstant at ho
  rw [hf, hf'] at ho
  rcases Int.lt_trichotomy (t.utcMinute * 61 + t.second) (t'.utcMinute * 61 + t'.second)
    with c | c | c
  · rw [Int.compare_eq_lt.mpr c] at ho; cases ho
  · exact c
  · rw [Int.compare_eq_gt.mpr c] at ho; cases ho

/-! ## The two directions -/

theorem fs_forward (n : Int) (t : Timestamp) (h : fromSiSeconds n = some t) :
    t.offset = .z ∧ t.fraction = [] ∧ Rfc3339.Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
      Rfc3339.Spec.siSeconds t = n := by
  by_cases hl : n ∈ leapSiSeconds
  · have hc := fs_check_leap n hl
    unfold fs_check at hc
    rw [h] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hz, hf⟩, hk⟩, hy⟩, hs⟩ := hc
    have hk' := (isValidKnown_iff t).mp hk
    exact ⟨hz, hf, hk', hy, by rw [← siSeconds_eq t hk'.1]; exact hs⟩
  · have hcont : leapSiSeconds.contains n = false := by
      cases e : leapSiSeconds.contains n
      · rfl
      · exact absurd (List.contains_iff_mem.mp e) hl
    unfold fromSiSeconds at h
    split at h
    · contradiction
    rename_i hn0
    simp only [hcont, Bool.false_eq_true, ite_false] at h
    obtain ⟨hv, hz, hf, h59, hu⟩ := (Rfc3339.Spec.fromUnixSeconds_iff _ _).mp h
    have hU : t.unixSeconds = n + 63072000 - (leapSiSeconds.filter (· < n)).length := by
      rw [Instant.unixSeconds_eq t hv]; exact hu
    obtain ⟨hk27, hc⟩ := fs_k_char n
    have hlb : t.leapsBefore = (leapSiSeconds.filter (· < n)).length := by
      rw [fs_leapsBefore_of_le59 t h59]
      apply fs_count_lt _ 27 _ hk27
      intro i hi
      rw [decide_eq_true_iff, hU]
      have := fs_V_le_iff n hl i hi
      constructor
      · intro a; exact this.mp (by omega)
      · intro a; have := this.mpr a; omega
    have hnk : ((leapSiSeconds.filter (· < n)).length : Int) ≤ n := by
      have key : ∀ k : Nat, k ≤ 27 → (∀ i, i < 27 → (fs_V i + i < n ↔ i < k)) →
          (k : Int) ≤ n := by
        intro k hk hc
        rcases Nat.eq_zero_or_pos k with e | e
        · subst e; omega
        · have h1 := (hc (k - 1) (by omega)).mpr (by omega)
          have h2 := fs_V_mono 0 (k - 1) (Nat.zero_le _) (by omega)
          rw [fs_V_zero] at h2
          omega
      exact key _ hk27 hc
    have hs : Rfc3339.Spec.siSeconds t = n := by
      rw [← siSeconds_eq t hv]
      unfold Timestamp.siSeconds
      rw [hU, hlb]
      omega
    refine ⟨hz, hf, ⟨hv, fun h60 => absurd h60 (by omega)⟩,
      fs_year_of_unix t hv hz h59 (by omega), hs⟩

theorem fs_isSome_of_bounds (n : Int) (h0 : 0 ≤ n) (h1 : n ≤ 253339228826) :
    (fromSiSeconds n).isSome := by
  obtain ⟨hk27, hc⟩ := fs_k_char n
  have h26 := hc 26 (by omega)
  rw [fs_V_last] at h26
  have hb : n + 63072000 - (leapSiSeconds.filter (· < n)).length ≤ 253402300799 := by
    by_cases c : (1420156800 : Int) + ((26 : Nat) : Int) < n
    · have := h26.mp c; omega
    · omega
  unfold fromSiSeconds
  split
  · exact absurd ‹n < 0› (by omega)
  dsimp only
  split
  · rw [Option.isSome_map]
    apply (Rfc3339.Spec.fromUnixSeconds_isSome _).mpr
    rw [FromUnix.fu_unixSeconds_lo, FromUnix.fu_unixSeconds_hi]
    omega
  · apply (Rfc3339.Spec.fromUnixSeconds_isSome _).mpr
    rw [FromUnix.fu_unixSeconds_lo, FromUnix.fu_unixSeconds_hi]
    omega

theorem fromSiSeconds_iff (n : Int) (t : Timestamp) :
    fromSiSeconds n = some t ↔
      t.offset = .z ∧ t.fraction = [] ∧ Rfc3339.Spec.ValidKnown t ∧ 1972 ≤ t.year ∧
        Rfc3339.Spec.siSeconds t = n := by
  constructor
  · exact fs_forward n t
  · rintro ⟨hz, hf, hk, hy, hs⟩
    have h0 : 0 ≤ n := hs ▸ fs_si_nonneg t hk.1 hz hy
    have h1 : n ≤ 253339228826 := by rw [← hs, ← fs_si_max]; exact fs_si_le_max t hk hz hf
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (fs_isSome_of_bounds n h0 h1)
    obtain ⟨hz', hf', hk', -, hs'⟩ := fs_forward n t' ht'
    rw [ht']
    congr 1
    exact (fs_eq_of_si t t' hk hk' hz hz' hf hf' (by rw [hs, hs'])).symm

theorem fromSiSeconds_isSome (n : Int) :
    (fromSiSeconds n).isSome ↔
      0 ≤ n ∧ n ≤ Rfc3339.Spec.siSeconds ⟨9999, 12, 31, 23, 59, 59, [], .z⟩ := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hz, hf, hk, hy, hs⟩ := fs_forward n t ht
    exact ⟨hs ▸ fs_si_nonneg t hk.1 hz hy, hs ▸ fs_si_le_max t hk hz hf⟩
  · rintro ⟨h0, h1⟩
    rw [fs_si_max] at h1
    exact fs_isSome_of_bounds n h0 h1

end Rfc3339.Proofs.Leap
