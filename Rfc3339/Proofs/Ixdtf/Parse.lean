/-
  `parseExt` and `Ext.print` against the grammar.
-/

import Rfc3339.Proofs.Ixdtf.Suffix
import Rfc3339.Proofs.Main

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

theorem px_digitChar_lt (n : Nat) : (Rfc3339.Spec.digitChar n).toNat < 91 := by
  unfold Rfc3339.Spec.digitChar
  rcases Nat.lt_or_ge n 10 with h | h
  · have : ∀ i : Fin 10, ("0123456789".toList.getD i.val '?').toNat < 91 := by decide
    exact this ⟨n, h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem px_digits_lt (k n : Nat) : ∀ c ∈ Rfc3339.Spec.digits k n, c.toNat < 91 := by
  intro c hc
  simp only [Rfc3339.Spec.digits, List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  exact px_digitChar_lt _

theorem px_renderOffset_lt (o : Offset) : ∀ c ∈ Rfc3339.Spec.renderOffset o, c.toNat < 91 := by
  cases o with
  | z => decide
  | plus h m | minus h m =>
    simp only [Rfc3339.Spec.renderOffset, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨⟨⟨by decide, by simp⟩, px_digits_lt _ _⟩, ⟨by decide, by simp⟩⟩, px_digits_lt _ _⟩

theorem px_render_lt (t : Timestamp) : ∀ c ∈ Rfc3339.Spec.render t, c.toNat < 91 := by
  simp only [Rfc3339.Spec.render, List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals first
    | exact px_digits_lt _ _
    | exact px_renderOffset_lt _
    | decide
    | (intro _ h; cases h)
    | skip
  split
  · simp
  · simp only [List.forall_mem_append, List.forall_mem_cons,
      List.forall_mem_map]
    exact ⟨⟨by decide, by simp⟩, fun _ _ => px_digitChar_lt _⟩

/-- A list whose upper case is a rendered timestamp has no `[`. -/
theorem px_no_bracket {dt : List Char} {t : Timestamp}
    (h : dt.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render t) : ∀ c ∈ dt, c ≠ '[' := by
  intro c hc hb
  subst hb
  have hm : Rfc3339.Spec.asciiUpper '[' ∈ Rfc3339.Spec.render t := h ▸ List.mem_map_of_mem hc
  have : Rfc3339.Spec.asciiUpper '[' = '[' := by decide
  rw [this] at hm
  have := px_render_lt t _ hm
  simp at this

theorem px_takeWhile_split {dt r : List Char} (hd : ∀ c ∈ dt, c ≠ '[')
    (hr : r = [] ∨ r.head? = some '[') :
    (dt ++ r).takeWhile (fun x => decide (x ≠ '[')) = dt := by
  rw [List.takeWhile_append_of_pos (by simpa using hd)]
  rcases hr with rfl | hr
  · simp
  · match r, hr with
    | _ :: _, hr =>
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr
      simp

theorem parseExt_iff (s : String) (e : Ext) :
    parseExt s = some e ↔
      Rfc3339.Spec.ExtValid e ∧ ∃ dt, s.toList = dt ++ Rfc3339.Spec.renderSuffix e ∧
        dt.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render e.stamp := by
  constructor
  · intro h
    simp only [parseExt, bind, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, ⟨zone, tags⟩, hs, he⟩ := h
    simp only [pure, Option.some.injEq] at he
    subst he
    obtain ⟨hv, hu⟩ := (Rfc3339.Spec.parse_iff _ t).mp ht
    rw [String.toList_ofList] at hu
    obtain ⟨⟨hz, htags⟩, hsuf⟩ :=
      (parseSuffix_iff _ ⟨t, zone, tags⟩).mp hs
    refine ⟨⟨hv, hz, htags⟩, _, ?_, hu⟩
    obtain ⟨r, hr⟩ := List.takeWhile_prefix (fun x => decide (x ≠ '[')) (l := s.toList)
    rw [← hsuf]
    generalize s.toList.takeWhile (fun x => decide (x ≠ '[')) = tw at hr ⊢
    rw [← hr, List.drop_left]
  · rintro ⟨⟨hv, hz, htags⟩, dt, hs, hu⟩
    have htw : s.toList.takeWhile (fun x => decide (x ≠ '[')) = dt := by
      rw [hs]; exact px_takeWhile_split (px_no_bracket hu) (renderSuffix_head e)
    have hp : parse (String.ofList dt) = some e.stamp :=
      (Rfc3339.Spec.parse_iff _ _).mpr ⟨hv, by rw [String.toList_ofList]; exact hu⟩
    have hsuf : parseSuffix (Rfc3339.Spec.renderSuffix e) = some (e.zone, e.tags) :=
      (parseSuffix_iff _ e).mpr ⟨⟨hz, htags⟩, rfl⟩
    simp only [parseExt, htw, hp]
    rw [hs, List.drop_left, hsuf]
    rfl

theorem printExt_eq (e : Ext) (h : Rfc3339.Spec.ExtValid e) :
    e.print.toList = Rfc3339.Spec.render e.stamp ++ Rfc3339.Spec.renderSuffix e := by
  rw [Ext.print, String.toList_ofList,
    Format.render_eq _ ((Rfc3339.Spec.isValid_iff _).mpr h.1), renderSuffix_eq e h.2.1]

theorem parseExt_print (e : Ext) (h : Rfc3339.Spec.ExtValid e) : parseExt e.print = some e :=
  (parseExt_iff _ e).mpr ⟨h, Rfc3339.Spec.render e.stamp, printExt_eq e h, Main.upper_render _⟩

theorem parseExt_plain (s : String) (h : '[' ∉ s.toList) :
    parseExt s = (parse s).map fun t => ⟨t, none, []⟩ := by
  have htw : s.toList.takeWhile (fun x => decide (x ≠ '[')) = s.toList := by
    have := px_takeWhile_split (dt := s.toList) (r := [])
      (fun c hc hb => h (hb ▸ hc)) (Or.inl rfl)
    simpa using this
  simp only [parseExt, htw, String.ofList_toList, List.drop_length]
  cases parse s <;> rfl

end Rfc3339.Proofs.Ixdtf
