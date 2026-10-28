/-
  The suffix parser against the grammar of RFC 9557, section 4.1.
-/

import Rfc3339
import Rfc3339.Spec.Ixdtf
import Rfc3339.Proofs.Format
import Rfc3339.Proofs.Valid

open Rfc3339

namespace Rfc3339.Proofs.Ixdtf

/-! ## Characters -/

theorem sx_alpha_ne {c : Char} (h : Rfc3339.Spec.Alpha c) :
    c ≠ ']' ∧ c ≠ '=' ∧ c ≠ '/' ∧ c ≠ '!' ∧ c ≠ '+' ∧ c ≠ '-' := by
  unfold Rfc3339.Spec.Alpha at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem sx_digit_ne {c : Char} (h : Rfc3339.Spec.Digit c) :
    c ≠ ']' ∧ c ≠ '=' ∧ c ≠ '/' ∧ c ≠ '!' ∧ c ≠ '+' ∧ c ≠ '-' := by
  unfold Rfc3339.Spec.Digit at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem sx_lower_ne {c : Char} (h : 'a' ≤ c ∧ c ≤ 'z') :
    c ≠ ']' ∧ c ≠ '=' ∧ c ≠ '/' ∧ c ≠ '!' ∧ c ≠ '+' ∧ c ≠ '-' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

theorem sx_zonePart_chars {p : List Char} (hp : Rfc3339.Spec.ZonePart p) :
    ∀ x ∈ p, x ≠ ']' ∧ x ≠ '=' ∧ x ≠ '/' := by
  obtain ⟨c, cs, rfl, hc, hcs, -, -⟩ := hp
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases hc with h | rfl | rfl
    · have := sx_alpha_ne h; exact ⟨this.1, this.2.1, this.2.2.1⟩
    all_goals decide
  · rcases hcs x hx with h | rfl | rfl | h | rfl | rfl
    · have := sx_alpha_ne h; exact ⟨this.1, this.2.1, this.2.2.1⟩
    · decide
    · decide
    · have := sx_digit_ne h; exact ⟨this.1, this.2.1, this.2.2.1⟩
    all_goals decide

theorem sx_zonePart_head {p : List Char} (hp : Rfc3339.Spec.ZonePart p) :
    ∃ c cs, p = c :: cs ∧ c ≠ '!' ∧ c ≠ '+' ∧ c ≠ '-' := by
  obtain ⟨c, cs, rfl, hc, -, -, -⟩ := hp
  refine ⟨c, cs, rfl, ?_⟩
  rcases hc with h | rfl | rfl
  · have := sx_alpha_ne h; exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩
  all_goals decide

theorem sx_key_chars {k : List Char} (hk : Rfc3339.Spec.SuffixKey k) : ∀ x ∈ k, x ≠ ']' ∧ x ≠ '=' := by
  obtain ⟨c, cs, rfl, hc, hcs⟩ := hk
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rcases hc with h | rfl
    · have := sx_lower_ne h; exact ⟨this.1, this.2.1⟩
    · decide
  · rcases hcs x hx with h | rfl | h | rfl
    · have := sx_lower_ne h; exact ⟨this.1, this.2.1⟩
    · decide
    · have := sx_digit_ne h; exact ⟨this.1, this.2.1⟩
    · decide

theorem sx_key_head {k : List Char} (hk : Rfc3339.Spec.SuffixKey k) : ∃ c cs, k = c :: cs ∧ c ≠ '!' := by
  obtain ⟨c, cs, rfl, hc, -⟩ := hk
  refine ⟨c, cs, rfl, ?_⟩
  rcases hc with h | rfl
  · exact (sx_lower_ne h).2.2.2.1
  · decide

theorem sx_value_chars {v : List Char} (hv : Rfc3339.Spec.SuffixValue v) :
    ∀ x ∈ v, x ≠ ']' ∧ x ≠ '=' ∧ x ≠ '-' := by
  intro x hx
  rcases hv.2 x hx with h | h
  · have := sx_alpha_ne h; exact ⟨this.1, this.2.1, this.2.2.2.2.2⟩
  · have := sx_digit_ne h; exact ⟨this.1, this.2.1, this.2.2.2.2.2⟩

theorem sx_alpha_iff (c : Char) : isAlpha c = true ↔ Rfc3339.Spec.Alpha c := by
  simp [isAlpha, Rfc3339.Spec.Alpha]
theorem sx_digit_iff (c : Char) : isDigitChar c = true ↔ Rfc3339.Spec.Digit c := by
  simp [isDigitChar, Rfc3339.Spec.Digit]
theorem sx_keyOK_iff (k : List Char) : keyOK k = true ↔ Rfc3339.Spec.SuffixKey k := by
  cases k with
  | nil => simp [keyOK, Rfc3339.Spec.SuffixKey]
  | cons c cs =>
    simp only [keyOK, Rfc3339.Spec.SuffixKey, sx_digit_iff, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq, List.cons.injEq]
    grind
theorem sx_valueOK_iff (v : List Char) : valueOK v = true ↔ Rfc3339.Spec.SuffixValue v := by
  simp only [valueOK, Rfc3339.Spec.SuffixValue, sx_digit_iff, sx_alpha_iff, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq]
theorem sx_drop_takeWhile (p : α → Bool) (xs : List α) : xs.drop (xs.takeWhile p).length = xs.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.takeWhile_cons, List.dropWhile_cons]
    cases p x <;> simp [ih]
theorem sx_takeWhile_append {p : α → Bool} (xs : List α) (y : α) (ys : List α)
    (hx : ∀ x ∈ xs, p x = true) (hy : p y = false) : (xs ++ y :: ys).takeWhile p = xs := by
  induction xs with
  | nil => simp [hy]
  | cons x xs ih =>
    simp only [List.cons_append, List.takeWhile_cons, hx x (by simp), ↓reduceIte]
    rw [ih (fun z hz => hx z (by simp [hz]))]
theorem sx_digitChar_mem (n : Nat) : Rfc3339.Spec.digitChar n ∈ "0123456789?".toList := by
  unfold Rfc3339.Spec.digitChar
  rw [List.getD_eq_getElem?_getD]
  cases h : "0123456789".toList[n]? with
  | none => decide
  | some x =>
    have := List.mem_of_getElem? h
    simp only [Option.getD_some]
    revert this; generalize x = y; revert y; decide
theorem sx_digits_mem {k n : Nat} {c : Char} (h : c ∈ Rfc3339.Spec.digits k n) : c ∈ "0123456789?".toList := by
  unfold Rfc3339.Spec.digits at h
  simp only [List.mem_map] at h
  obtain ⟨i, _, rfl⟩ := h
  exact sx_digitChar_mem _
theorem sx_mem_join {α : Type} {s : List α} {ls : List (List α)} {x : α}
    (h : x ∈ (ls.intersperse s).flatten) : x ∈ s ∨ ∃ l ∈ ls, x ∈ l := by
  induction ls with
  | nil => simp at h
  | cons a tl ih =>
    cases tl with
    | nil => exact Or.inr ⟨a, by simp, by simpa using h⟩
    | cons b rest =>
      rw [List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons, List.mem_append,
        List.mem_append] at h
      rcases h with h | h | h
      · exact Or.inr ⟨a, by simp, h⟩
      · exact Or.inl h
      · rcases ih h with h' | ⟨l, hl, hx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, hx⟩

theorem sx_join_cons {α : Type} (s p : List α) (rest : List (List α)) :
    ∃ X, ((p :: rest).intersperse s).flatten = p ++ X := by
  cases rest with
  | nil => exact ⟨[], by simp⟩
  | cons b rest => exact ⟨_, by rw [List.intersperse_cons_cons, List.flatten_cons]⟩

theorem sx_intercalate_eq {α : Type} (s : List α) (ls : List (List α)) :
    s.intercalate ls = (ls.intersperse s).flatten := rfl

theorem sx_zonePartOK_iff (p : List Char) : zonePartOK p = true ↔ Rfc3339.Spec.ZonePart p := by
  cases p with
  | nil => simp [zonePartOK, Rfc3339.Spec.ZonePart]
  | cons c cs =>
    simp only [zonePartOK, Rfc3339.Spec.ZonePart, sx_alpha_iff, sx_digit_iff, Bool.and_eq_true,
      Bool.or_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.cons.injEq]
    grind

/-- The body of a tag item, after the flag. -/
def sx_tagBody (t : Tag) : List Char := t.key ++ ['='] ++ (t.values.intersperse ['-']).flatten

/-- An item: brackets around the flag and the body. -/
def sx_item (c : Bool) (b : List Char) : List Char := ['['] ++ Rfc3339.Spec.renderFlag c ++ b ++ [']']

theorem sx_parseTag_sound {c : Bool} {b : List Char} {t : Tag} (h : parseTag c b = some t) :
    Rfc3339.Spec.TagValid t ∧ t.critical = c ∧ b = sx_tagBody t := by
  unfold parseTag at h
  have hb := (sx_drop_takeWhile (fun x => decide (x ≠ '=')) b).symm ▸
    (List.takeWhile_append_dropWhile (p := fun x => decide (x ≠ '=')) (l := b))
  dsimp only at h
  split at h
  · rename_i vs hvs
    split at h
    · rename_i hok
      injection h with h
      subst h
      simp only [Bool.and_eq_true, List.all_eq_true, sx_keyOK_iff, sx_valueOK_iff] at hok
      refine ⟨⟨hok.1, List.splitOn_ne_nil _ _, hok.2⟩, rfl, ?_⟩
      rw [hvs] at hb
      simp only [sx_tagBody, ← sx_intercalate_eq, List.intercalate_splitOn]
      rw [List.append_assoc, List.singleton_append]
      exact hb.symm
    · simp at h
  · simp at h

theorem sx_parseTag_render {t : Tag} (h : Rfc3339.Spec.TagValid t) :
    parseTag t.critical (sx_tagBody t) = some t := by
  obtain ⟨hk, hne, hv⟩ := h
  have hkey : (sx_tagBody t).takeWhile (fun x => decide (x ≠ '=')) = t.key := by
    unfold sx_tagBody
    rw [List.append_assoc, List.singleton_append]
    exact sx_takeWhile_append _ _ _ (fun x hx => by simpa using (sx_key_chars hk x hx).2)
      (by simp)
  unfold parseTag
  simp only [hkey]
  unfold sx_tagBody
  rw [List.append_assoc, List.drop_left, List.singleton_append]
  simp only
  rw [← sx_intercalate_eq, List.splitOn_intercalate _ (fun l hl => by
    intro hm; exact (sx_value_chars (hv l hl) _ hm).2.2 rfl) hne]
  have hkok : keyOK t.key = true := (sx_keyOK_iff _).mpr hk
  have hvok : t.values.all valueOK = true := List.all_eq_true.mpr fun v hv' => (sx_valueOK_iff v).mpr (hv v hv')
  simp [hkok, hvok]

theorem sx_parseZone_sound {b : List Char} {z : Zone} (h : parseZone b = some z) :
    Rfc3339.Spec.ZoneValid z ∧ b = Rfc3339.Spec.renderZone z := by
  unfold parseZone at h
  split at h
  · rename_i x
    split at h
    · rename_i o ho
      split at h
      · rename_i hvo
        injection h with h
        subst h
        have hb := Rfc3339.Proofs.Format.parseOffset_spec ho
        refine ⟨⟨?_, (Rfc3339.Proofs.Valid.offset_isValid_iff o).mp hvo⟩, ?_⟩
        · rintro rfl; simp [Offset.render] at hb
        · rw [hb]; exact Rfc3339.Proofs.Format.offset_render_eq o
      · simp at h
    · simp at h
  · rename_i x
    split at h
    · rename_i o ho
      split at h
      · rename_i hvo
        injection h with h
        subst h
        have hb := Rfc3339.Proofs.Format.parseOffset_spec ho
        refine ⟨⟨?_, (Rfc3339.Proofs.Valid.offset_isValid_iff o).mp hvo⟩, ?_⟩
        · rintro rfl; simp [Offset.render] at hb
        · rw [hb]; exact Rfc3339.Proofs.Format.offset_render_eq o
      · simp at h
    · simp at h
  · dsimp only at h
    split at h
    · rename_i hall
      injection h with h
      subst h
      refine ⟨⟨List.splitOn_ne_nil _ _, fun p hp => (sx_zonePartOK_iff p).mp (List.all_eq_true.mp hall p hp)⟩, ?_⟩
      show b = ((b.splitOn '/').intersperse ['/']).flatten
      rw [← sx_intercalate_eq, List.intercalate_splitOn]
    · simp at h

theorem sx_parseZone_render {z : Zone} (h : Rfc3339.Spec.ZoneValid z) :
    parseZone (Rfc3339.Spec.renderZone z) = some z := by
  cases z with
  | name parts =>
    obtain ⟨hne, hp⟩ := h
    obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨c, cs, hpc, hc1, hc2, hc3⟩ := sx_zonePart_head (hp p (by simp))
    obtain ⟨X, hX⟩ := sx_join_cons ['/'] p rest
    have hsplit : ((p :: rest).intersperse ['/']).flatten.splitOn '/' = p :: rest := by
      rw [← sx_intercalate_eq]
      exact List.splitOn_intercalate _
        (fun l hl hm => (sx_zonePart_chars (hp l hl) _ hm).2.2 rfl) (by simp)
    have hall : (p :: rest).all zonePartOK = true :=
      List.all_eq_true.mpr fun l hl => (sx_zonePartOK_iff l).mpr (hp l hl)
    show parseZone ((p :: rest).intersperse ['/']).flatten = _
    unfold parseZone
    split
    · rename_i x heq
      rw [hX, hpc] at heq
      simp at heq
      exact absurd heq.1 hc2
    · rename_i x heq
      rw [hX, hpc] at heq
      simp at heq
      exact absurd heq.1 hc3
    · simp only [hsplit, hall]
      rfl
  | offset o =>
    obtain ⟨hz, hv⟩ := h
    have hvalid : o.isValid = true := (Rfc3339.Proofs.Valid.offset_isValid_iff o).mpr hv
    have hr := Rfc3339.Proofs.Format.parseOffset_render o hvalid
    show parseZone (Rfc3339.Spec.renderOffset o) = _
    rw [← Rfc3339.Proofs.Format.offset_render_eq]
    cases o with
    | z => exact absurd rfl hz
    | plus a m =>
      have hcons : (Offset.plus a m).render = '+' :: (pad2 a ++ ':' :: pad2 m) := rfl
      rw [hcons] at hr ⊢
      unfold parseZone
      simp only [hr, hvalid, ↓reduceIte]
    | minus a m =>
      have hcons : (Offset.minus a m).render = '-' :: (pad2 a ++ ':' :: pad2 m) := rfl
      rw [hcons] at hr ⊢
      unfold parseZone
      simp only [hr, hvalid, ↓reduceIte]


theorem sx_digits_ne {k n : Nat} {c : Char} (h : c ∈ Rfc3339.Spec.digits k n) : c ≠ ']' ∧ c ≠ '=' := by
  have key : ∀ d ∈ "0123456789?".toList, d ≠ ']' ∧ d ≠ '=' := by decide
  exact key c (sx_digits_mem h)

theorem sx_tagBody_facts {t : Tag} (h : Rfc3339.Spec.TagValid t) :
    ']' ∉ sx_tagBody t ∧ (sx_tagBody t).head? ≠ some '!' ∧ '=' ∈ sx_tagBody t := by
  obtain ⟨hk, hne, hv⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold sx_tagBody
    simp only [List.mem_append, not_or]
    refine ⟨⟨fun hm => (sx_key_chars hk _ hm).1 rfl, by decide⟩, fun hm => ?_⟩
    rcases sx_mem_join hm with h | ⟨l, hl, hx⟩
    · simp at h
    · exact (sx_value_chars (hv l hl) _ hx).1 rfl
  · obtain ⟨c, cs, hkc, hc⟩ := sx_key_head hk
    unfold sx_tagBody
    rw [hkc]
    simpa using hc
  · unfold sx_tagBody
    simp

theorem sx_zoneBody_facts {z : Zone} (h : Rfc3339.Spec.ZoneValid z) :
    ']' ∉ Rfc3339.Spec.renderZone z ∧ (Rfc3339.Spec.renderZone z).head? ≠ some '!' ∧ '=' ∉ Rfc3339.Spec.renderZone z := by
  cases z with
  | name parts =>
    obtain ⟨hne, hp⟩ := h
    refine ⟨fun hm => ?_, ?_, fun hm => ?_⟩
    · rcases sx_mem_join hm with h | ⟨l, hl, hx⟩
      · simp at h
      · exact (sx_zonePart_chars (hp l hl) _ hx).1 rfl
    · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨c, cs, hpc, hc1, -, -⟩ := sx_zonePart_head (hp p (by simp))
      obtain ⟨X, hX⟩ := sx_join_cons ['/'] p rest
      show (((p :: rest).intersperse ['/']).flatten).head? ≠ _
      rw [hX, hpc]
      simpa using hc1
    · rcases sx_mem_join hm with h | ⟨l, hl, hx⟩
      · simp at h
      · exact (sx_zonePart_chars (hp l hl) _ hx).2.1 rfl
  | offset o =>
    obtain ⟨hz, -⟩ := h
    cases o with
    | z => exact absurd rfl hz
    | plus a m =>
      refine ⟨fun hm => ?_, by simp [Rfc3339.Spec.renderZone, Rfc3339.Spec.renderOffset], fun hm => ?_⟩ <;>
      · simp only [Rfc3339.Spec.renderZone, Rfc3339.Spec.renderOffset, List.mem_append] at hm
        rcases hm with ((h | h) | h) | h <;>
          first
            | exact absurd h (by decide)
            | exact (sx_digits_ne h).1 rfl
            | exact (sx_digits_ne h).2 rfl
    | minus a m =>
      refine ⟨fun hm => ?_, by simp [Rfc3339.Spec.renderZone, Rfc3339.Spec.renderOffset], fun hm => ?_⟩ <;>
      · simp only [Rfc3339.Spec.renderZone, Rfc3339.Spec.renderOffset, List.mem_append] at hm
        rcases hm with ((h | h) | h) | h <;>
          first
            | exact absurd h (by decide)
            | exact (sx_digits_ne h).1 rfl
            | exact (sx_digits_ne h).2 rfl

theorem sx_suffixItems_cons (f : Nat) (c : Bool) (b R : List Char) (hb : ']' ∉ b)
    (hh : b.head? ≠ some '!') :
    suffixItems (f + 1) (sx_item c b ++ R) = (suffixItems f R).map (fun tail => (c, b) :: tail) := by
  have hB : ∀ x ∈ Rfc3339.Spec.renderFlag c ++ b, decide (x ≠ ']') = true := by
    intro x hx
    simp only [decide_eq_true_eq]
    rintro rfl
    rcases List.mem_append.mp hx with h | h
    · cases c <;> simp [Rfc3339.Spec.renderFlag] at h
    · exact hb h
  have e1 : sx_item c b ++ R = '[' :: ((Rfc3339.Spec.renderFlag c ++ b) ++ ']' :: R) := by simp [sx_item]
  rw [e1]
  simp only [suffixItems, ↓reduceIte]
  rw [sx_takeWhile_append _ _ _ hB (by simp), List.drop_left]
  simp only
  cases c with
  | true =>
    cases suffixItems f R <;> rfl
  | false =>
    cases hs : suffixItems f R with
    | none => rfl
    | some tail =>
      simp only [Rfc3339.Spec.renderFlag, Bool.false_eq_true, ↓reduceIte, List.nil_append, Option.map_some]
      split
      · simp at hh
      · rfl


theorem sx_suffixItems_render (items : List (Bool × List Char)) (fuel : Nat)
    (h : ∀ p ∈ items, ']' ∉ p.2 ∧ p.2.head? ≠ some '!')
    (hf : (items.flatMap (fun p => sx_item p.1 p.2)).length ≤ fuel) :
    suffixItems fuel (items.flatMap (fun p => sx_item p.1 p.2)) = some items := by
  induction items generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons p rest ih =>
    obtain ⟨c, b⟩ := p
    simp only [List.flatMap_cons] at hf ⊢
    have hlen : (sx_item c b).length ≥ 2 := by simp [sx_item]; omega
    simp only [List.length_append] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hp := h (c, b) (by simp)
    rw [sx_suffixItems_cons f c b _ hp.1 hp.2,
      ih f (fun q hq => h q (List.mem_cons_of_mem _ hq)) (by omega)]
    rfl

theorem sx_suffixItems_sound (fuel : Nat) (cs : List Char) (items : List (Bool × List Char))
    (h : suffixItems fuel cs = some items) :
    cs = items.flatMap (fun p => sx_item p.1 p.2) := by
  induction fuel generalizing cs items with
  | zero =>
    cases cs with
    | nil =>
      simp only [suffixItems, Option.some.injEq] at h
      subst h; rfl
    | cons c rest => simp [suffixItems] at h
  | succ f ih =>
    cases cs with
    | nil =>
      simp only [suffixItems, Option.some.injEq] at h
      subst h; rfl
    | cons c rest =>
      have hr := (sx_drop_takeWhile (fun x => decide (x ≠ ']')) rest).symm ▸
        (List.takeWhile_append_dropWhile (p := fun x => decide (x ≠ ']')) (l := rest))
      unfold suffixItems at h
      split at h
      · rename_i hc
        subst hc
        dsimp only at h
        split at h
        · rename_i more hmore
          rw [hmore] at hr
          obtain ⟨tail, ht, h2⟩ := Option.bind_eq_some_iff.mp h
          clear h
          have := ih more tail ht
          subst this
          split at h2
          · rename_i b hbody
            simp only [pure, Option.some.injEq] at h2
            subst h2
            rw [hbody] at hr
            subst hr
            simp [sx_item, Rfc3339.Spec.renderFlag]
          · simp only [pure, Option.some.injEq] at h2
            subst h2
            obtain ⟨B, hB⟩ : ∃ B, List.takeWhile (fun x => decide (x ≠ ']')) rest = B := ⟨_, rfl⟩
            rw [hB] at hr ⊢
            subst hr
            simp [sx_item, Rfc3339.Spec.renderFlag]
        · simp at h
      · simp at h


theorem sx_mapM_sound (rest : List (Bool × List Char)) (tags : List Tag)
    (h : rest.mapM (fun (c, b) => parseTag c b) = some tags) :
    (∀ t ∈ tags, Rfc3339.Spec.TagValid t) ∧ rest = tags.map (fun t => (t.critical, sx_tagBody t)) := by
  induction rest generalizing tags with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | cons p rest ih =>
    obtain ⟨c, b⟩ := p
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨t, ht, ts, hts, rfl⟩ := h
    obtain ⟨htv, rfl, rfl⟩ := sx_parseTag_sound ht
    obtain ⟨hv, rfl⟩ := ih ts hts
    refine ⟨?_, rfl⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact htv
    · exact hv u hu

theorem sx_mapM_render (tags : List Tag) (h : ∀ t ∈ tags, Rfc3339.Spec.TagValid t) :
    (tags.map (fun t => (t.critical, sx_tagBody t))).mapM (fun (c, b) => parseTag c b) =
      some tags := by
  induction tags with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mapM_cons, sx_parseTag_render (h t (by simp)),
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    rfl

/-- The items of a suffix: the time zone, if any, then the tags. -/
def sx_items (e : Ext) : List (Bool × List Char) :=
  (match e.zone with
   | some (c, z) => [(c, Rfc3339.Spec.renderZone z)]
   | none => []) ++ e.tags.map (fun t => (t.critical, sx_tagBody t))

theorem sx_renderTag_eq (t : Tag) : Rfc3339.Spec.renderTag t = sx_item t.critical (sx_tagBody t) := by
  simp [Rfc3339.Spec.renderTag, sx_item, sx_tagBody]

theorem sx_renderSuffix_items (e : Ext) :
    Rfc3339.Spec.renderSuffix e = (sx_items e).flatMap (fun p => sx_item p.1 p.2) := by
  obtain ⟨stamp, zone, tags⟩ := e
  have htags : (tags.map Rfc3339.Spec.renderTag).flatten =
      (tags.map (fun t => (t.critical, sx_tagBody t))).flatMap (fun p => sx_item p.1 p.2) := by
    induction tags with
    | nil => rfl
    | cons t ts ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih, sx_renderTag_eq]
  rcases zone with _ | ⟨c, z⟩
  · simp only [Rfc3339.Spec.renderSuffix, sx_items, List.nil_append, htags]
  · simp only [Rfc3339.Spec.renderSuffix, sx_items, htags, List.singleton_append, List.flatMap_cons, sx_item]

theorem sx_items_facts (e : Ext) (hz : ∀ c z, e.zone = some (c, z) → Rfc3339.Spec.ZoneValid z)
    (ht : ∀ t ∈ e.tags, Rfc3339.Spec.TagValid t) :
    ∀ p ∈ sx_items e, ']' ∉ p.2 ∧ p.2.head? ≠ some '!' := by
  obtain ⟨stamp, zone, tags⟩ := e
  intro p hp
  simp only [sx_items, List.mem_append, List.mem_map] at hp
  rcases hp with hp | ⟨t, htm, rfl⟩
  · rcases zone with _ | ⟨c, z⟩
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      have := sx_zoneBody_facts (hz c z rfl)
      exact ⟨this.1, this.2.1⟩
  · have := sx_tagBody_facts (ht t htm)
    exact ⟨this.1, this.2.1⟩

/-- `parseSuffix` reads exactly the suffixes of the grammar, as
    `Rfc3339.Spec.renderSuffix` writes them. -/
theorem parseSuffix_iff (cs : List Char) (e : Ext) :
    parseSuffix cs = some (e.zone, e.tags) ↔
      ((∀ c z, e.zone = some (c, z) → Rfc3339.Spec.ZoneValid z) ∧ ∀ t ∈ e.tags, Rfc3339.Spec.TagValid t) ∧
        cs = Rfc3339.Spec.renderSuffix e := by
  constructor
  · intro h
    unfold parseSuffix at h
    obtain ⟨items, hitems, h2⟩ := Option.bind_eq_some_iff.mp h
    clear h
    have hcs := sx_suffixItems_sound _ _ _ hitems
    clear hitems
    subst hcs
    rw [sx_renderSuffix_items]
    obtain ⟨stamp, zone, tags⟩ := e
    simp only at h2 ⊢
    match items, h2 with
    | [], h =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [sx_items]
    | (crit, body) :: rest, h =>
      obtain ⟨tags', htags, h3⟩ := Option.bind_eq_some_iff.mp h
      clear h
      obtain ⟨hv', rfl⟩ := sx_mapM_sound rest tags' htags
      split at h3
      · obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h3
        clear h3
        obtain ⟨htv, rfl, rfl⟩ := sx_parseTag_sound ht
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨by simp, ?_⟩, by simp [sx_items]⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact htv
        · exact hv' u hu
      · obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h3
        clear h3
        obtain ⟨hzv, rfl⟩ := sx_parseZone_sound hz
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨?_, hv'⟩, by simp [sx_items]⟩
        intro c z' hcz
        simp only [Option.some.injEq, Prod.mk.injEq] at hcz
        obtain ⟨rfl, rfl⟩ := hcz
        exact hzv
  · rintro ⟨⟨hz, ht⟩, rfl⟩
    have hf := sx_items_facts e hz ht
    rw [sx_renderSuffix_items]
    unfold parseSuffix
    rw [sx_suffixItems_render _ _ hf (Nat.le_refl _)]
    obtain ⟨stamp, zone, tags⟩ := e
    simp only at hz ht ⊢
    rcases zone with _ | ⟨c, z⟩
    · cases tags with
      | nil => rfl
      | cons t ts =>
        have htv := ht t (by simp)
        have hts : ∀ u ∈ ts, Rfc3339.Spec.TagValid u := fun u hu => ht u (List.mem_cons_of_mem _ hu)
        have hc : (sx_tagBody t).contains '=' = true :=
          List.contains_iff_mem.mpr (sx_tagBody_facts htv).2.2
        simp only [sx_items, List.nil_append, List.map_cons, Option.bind_eq_bind, Option.bind_some]
        simp only [Option.bind_some, sx_mapM_render ts hts, hc, ↓reduceIte, sx_parseTag_render htv]
        rfl
    · have hzv := hz c z rfl
      have hc : (Rfc3339.Spec.renderZone z).contains '=' = false := by
        cases h : (Rfc3339.Spec.renderZone z).contains '=' with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp h) (sx_zoneBody_facts hzv).2.2
      simp only [sx_items, List.singleton_append]
      simp only [bind, Option.bind_some, sx_mapM_render tags ht, hc, Bool.false_eq_true, ↓reduceIte,
        sx_parseZone_render hzv]
      rfl

/-- The code's rendering of the suffix is the spec's. -/
theorem renderSuffix_eq (e : Ext) (h : ∀ c z, e.zone = some (c, z) → Rfc3339.Spec.ZoneValid z) :
    e.renderSuffix = Rfc3339.Spec.renderSuffix e := by
  obtain ⟨stamp, zone, tags⟩ := e
  have hz : ∀ z : Zone, z.render = Rfc3339.Spec.renderZone z := by
    intro z
    cases z with
    | name parts => rfl
    | offset o => exact Rfc3339.Proofs.Format.offset_render_eq o
  have ht : (Tag.render : Tag → List Char) = Rfc3339.Spec.renderTag := funext fun t => rfl
  simp only [Ext.renderSuffix, Rfc3339.Spec.renderSuffix, List.flatMap_def, ht]
  rcases zone with _ | ⟨c, z⟩
  · rfl
  · simp only [hz]
    rfl

/-- A suffix of the grammar is empty or starts with `[`, and holds no
    other `[` than at the start of each item; in particular a rendered
    suffix starts with `[` when it is not empty. -/
theorem renderSuffix_head (e : Ext) :
    Rfc3339.Spec.renderSuffix e = [] ∨ (Rfc3339.Spec.renderSuffix e).head? = some '[' := by
  obtain ⟨stamp, zone, tags⟩ := e
  rcases zone with _ | ⟨c, z⟩
  · cases tags with
    | nil => left; rfl
    | cons t ts => right; simp [Rfc3339.Spec.renderSuffix, Rfc3339.Spec.renderTag]
  · right
    simp [Rfc3339.Spec.renderSuffix]

end Rfc3339.Proofs.Ixdtf
