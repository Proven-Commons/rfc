/-
  The statements of `Rfc3339/Spec.lean`, under the same names, from the lemmas
  in the other files of `Rfc3339/Proofs/`. The test vectors are checked by
  evaluation.
-/

import Rfc3339
import Rfc3339.Spec.Defs
import Rfc3339.Proofs.Valid
import Rfc3339.Proofs.Format
import Rfc3339.Proofs.Instant

open Rfc3339

namespace Rfc3339.Proofs.Main

/-- Every character `Rfc3339.Spec.render` writes is below `a`, so upper case
    leaves it alone. -/
theorem upper_fixed (c : Char) (h : c.toNat < 97) : Rfc3339.Spec.asciiUpper c = c := by
  unfold Rfc3339.Spec.asciiUpper
  simp only [ite_eq_right_iff]
  omega

theorem digitChar_lt (n : Nat) : (Rfc3339.Spec.digitChar n).toNat < 97 := by
  unfold Rfc3339.Spec.digitChar
  rcases Nat.lt_or_ge n 10 with h | h
  · have : ∀ i : Fin 10, ("0123456789".toList.getD i.val '?').toNat < 97 := by decide
    exact this ⟨n, h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem digits_lt (k n : Nat) : ∀ c ∈ Rfc3339.Spec.digits k n, c.toNat < 97 := by
  intro c hc
  simp only [Rfc3339.Spec.digits, List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  exact digitChar_lt _

theorem renderOffset_lt (o : Offset) : ∀ c ∈ Rfc3339.Spec.renderOffset o, c.toNat < 97 := by
  cases o with
  | z => decide
  | plus h m | minus h m =>
    simp only [Rfc3339.Spec.renderOffset, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨⟨⟨by decide, by simp⟩, digits_lt _ _⟩, ⟨by decide, by simp⟩⟩, digits_lt _ _⟩

theorem render_lt (t : Timestamp) : ∀ c ∈ Rfc3339.Spec.render t, c.toNat < 97 := by
  simp only [Rfc3339.Spec.render, List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals first
    | exact digits_lt _ _
    | exact renderOffset_lt _
    | decide
    | (intro _ h; cases h)
    | skip
  split
  · simp
  · simp only [List.forall_mem_append, List.forall_mem_cons,
      List.forall_mem_map]
    exact ⟨⟨by decide, by simp⟩, fun _ _ => digitChar_lt _⟩

theorem upper_render (t : Timestamp) : (Rfc3339.Spec.render t).map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render t := by
  conv => rhs; rw [← List.map_id (Rfc3339.Spec.render t)]
  exact List.map_congr_left fun c hc => upper_fixed c (render_lt t c hc)

end Rfc3339.Proofs.Main

open Rfc3339.Proofs

theorem Rfc3339.Spec.isValid_iff (t : Timestamp) : t.isValid = true ↔ Rfc3339.Spec.Valid t :=
  Valid.isValid_iff t

theorem Rfc3339.Spec.print_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.print.toList = Rfc3339.Spec.render t := by
  rw [Format.print_toList, Format.render_eq t ((Rfc3339.Spec.isValid_iff t).mpr h)]

theorem Rfc3339.Spec.parse_iff (s : String) (t : Timestamp) :
    parse s = some t ↔ Rfc3339.Spec.Valid t ∧ s.toList.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render t := by
  rw [Format.parse_iff', Rfc3339.Spec.isValid_iff]

theorem Rfc3339.Spec.parse_valid (s : String) (t : Timestamp) (h : parse s = some t) :
    Rfc3339.Spec.Valid t :=
  ((Rfc3339.Spec.parse_iff s t).mp h).1

theorem Rfc3339.Spec.parse_print (t : Timestamp) (h : Rfc3339.Spec.Valid t) : parse t.print = some t := by
  rw [Rfc3339.Spec.parse_iff, Rfc3339.Spec.print_eq t h]
  exact ⟨h, Main.upper_render t⟩

theorem Rfc3339.Spec.print_parse (s : String) (t : Timestamp) (h : parse s = some t) :
    t.print.toList = s.toList.map Rfc3339.Spec.asciiUpper := by
  obtain ⟨hv, hs⟩ := (Rfc3339.Spec.parse_iff s t).mp h
  rw [Rfc3339.Spec.print_eq t hv, hs]

theorem Rfc3339.Spec.unixSeconds_eq (t : Timestamp) (h : Rfc3339.Spec.Valid t) :
    t.unixSeconds = Rfc3339.Spec.unixSeconds t :=
  Instant.unixSeconds_eq t h

theorem Rfc3339.Spec.compareInstant_eq (a b : Timestamp) (ha : Rfc3339.Spec.Valid a) (hb : Rfc3339.Spec.Valid b) :
    a.compareInstant b = Rfc3339.Spec.compareInstants a b :=
  Instant.compareInstant_eq a b ha hb

theorem Rfc3339.Spec.rfc3339_examples :
    parse "1985-04-12T23:20:50.52Z" = some ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ ∧
    parse "1996-12-19T16:39:57-08:00" = some ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩ ∧
    parse "1990-12-31T23:59:60Z" = some ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ ∧
    parse "1990-12-31T15:59:60-08:00" = some ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ ∧
    parse "1937-01-01T12:00:27.87+00:20" =
      some ⟨1937, 1, 1, 12, 0, 27, [8, 7], .plus 0 20⟩ := by
  decide

theorem Rfc3339.Spec.rfc3339_example_instants :
    (Timestamp.compareInstant ⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩
      ⟨1996, 12, 20, 0, 39, 57, [], .z⟩ = .eq) ∧
    (Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1990, 12, 31, 15, 59, 60, [], .minus 8 0⟩ = .eq) ∧
    Timestamp.unixSeconds ⟨1985, 4, 12, 23, 20, 50, [5, 2], .z⟩ = 482196050 := by
  -- `compareFraction` is defined by well-founded recursion, which `decide`
  -- does not unfold, so the orders go through `Rfc3339.Spec.compareInstant_eq`.
  refine ⟨?_, ?_, by decide⟩
  all_goals
    rw [Rfc3339.Spec.compareInstant_eq _ _ ((Rfc3339.Spec.isValid_iff _).mp (by decide))
      ((Rfc3339.Spec.isValid_iff _).mp (by decide))]
    decide +kernel

theorem Rfc3339.Spec.leap_second_order :
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 59, [9], .z⟩
      ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [5], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [2], .z⟩ = .lt ∧
    Timestamp.compareInstant ⟨1990, 12, 31, 23, 59, 60, [], .z⟩
      ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ = .lt ∧
    Timestamp.unixSeconds ⟨1990, 12, 31, 23, 59, 60, [], .z⟩ =
      Timestamp.unixSeconds ⟨1991, 1, 1, 0, 0, 0, [], .z⟩ := by
  refine ⟨?_, ?_, ?_, by decide⟩
  all_goals
    rw [Rfc3339.Spec.compareInstant_eq _ _ ((Rfc3339.Spec.isValid_iff _).mp (by decide))
      ((Rfc3339.Spec.isValid_iff _).mp (by decide))]
    decide +kernel

theorem Rfc3339.Spec.calendar_vectors :
    (parse "2000-02-29T00:00:00Z").isSome ∧
    (parse "2004-02-29T00:00:00Z").isSome ∧
    parse "1900-02-29T00:00:00Z" = none ∧
    parse "2001-02-29T00:00:00Z" = none ∧
    parse "2000-02-30T00:00:00Z" = none ∧
    parse "2001-04-31T00:00:00Z" = none ∧
    parse "2001-01-32T00:00:00Z" = none ∧
    parse "2001-01-00T00:00:00Z" = none ∧
    parse "2001-00-01T00:00:00Z" = none ∧
    parse "2001-13-01T00:00:00Z" = none := by
  decide

theorem Rfc3339.Spec.leap_second_vectors :
    (parse "1990-06-30T23:59:60Z").isSome ∧
    (parse "1991-01-01T00:59:60+01:00").isSome ∧
    parse "1990-12-31T23:59:61Z" = none ∧
    parse "1990-12-31T23:58:60Z" = none ∧
    parse "1990-12-30T23:59:60Z" = none ∧
    parse "1990-12-31T23:59:60+01:00" = none := by
  decide

theorem Rfc3339.Spec.syntax_vectors :
    parse "1985-04-12t23:20:50.52z" = parse "1985-04-12T23:20:50.52Z" ∧
    parse "1985-04-12 23:20:50.52Z" = none ∧
    parse "1985-04-12T23:20:50.Z" = none ∧
    parse "1985-04-12T23:20:50,52Z" = none ∧
    parse "1985-04-12T23:20Z" = none ∧
    parse "85-04-12T23:20:50Z" = none ∧
    parse "1985-04-12T23:20:50+24:00" = none ∧
    parse "1985-04-12T23:20:50+23:60" = none ∧
    parse "1985-04-12T23:20:50+0100" = none ∧
    parse "1985-04-12T23:20:50" = none ∧
    parse "1985-04-12T23:20:50Z " = none ∧
    parse "1985-04-12T24:00:00Z" = none := by
  decide
