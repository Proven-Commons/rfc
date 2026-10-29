/-
  The printer and the parser of `Rfc3339/Format.lean` against the spec:
  `asciiUpper` is `Rfc3339.Spec.asciiUpper`, a valid timestamp renders as
  `Rfc3339.Spec.render` writes it, and `parseUpper` returns `t` exactly when `t`
  is valid and the input is `t.render`. From these, `parse_iff'`.
-/

import Rfc3339
import Rfc3339.Spec.Defs

namespace Rfc3339.Proofs.Format

open Rfc3339

/-! ## Characters and printing -/

/-- `Char` order is the order of code points. -/
theorem le_iff_toNat (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

theorem asciiUpper_eq (c : Char) : asciiUpper c = Rfc3339.Spec.asciiUpper c := by
  unfold asciiUpper Rfc3339.Spec.asciiUpper
  simp only [le_iff_toNat]
  rfl

theorem print_toList (t : Timestamp) : t.print.toList = t.render := by
  simp [Timestamp.print]

theorem digitChar_eq (n : Nat) (h : n < 10) : Rfc3339.Spec.digitChar n = digitChar n := by
  have : ∀ i : Fin 10, Rfc3339.Spec.digitChar i.val = digitChar i.val := by decide
  exact this ⟨n, h⟩

/-- `pad4` and `pad2` write the last digits of any number, as `Rfc3339.Spec.digits` does. -/
theorem digits4 (n : Nat) : Rfc3339.Spec.digits 4 n = pad4 n := by
  simp [Rfc3339.Spec.digits, pad4, List.range, List.range.loop, digitChar_eq, Nat.mod_lt]

theorem digits2 (n : Nat) : Rfc3339.Spec.digits 2 n = pad2 n := by
  simp [Rfc3339.Spec.digits, pad2, List.range, List.range.loop, digitChar_eq, Nat.mod_lt]

theorem daysInMonth_le (y m : Nat) : daysInMonth y m ≤ 31 := by
  unfold daysInMonth
  split <;> (try split) <;> omega

/-- The bounds on the fields that printing and parsing need. -/
theorem isValid_bounds {t : Timestamp} (h : t.isValid = true) :
    t.year ≤ 9999 ∧ t.month ≤ 12 ∧ t.day ≤ 31 ∧ t.hour ≤ 23 ∧ t.minute ≤ 59 ∧ t.second ≤ 60 ∧
    (∀ d ∈ t.fraction, d < 10) ∧ t.offset.isValid = true := by
  simp only [Timestamp.isValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have := daysInMonth_le t.year t.month
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | simp_all

theorem renderFraction_eq (f : List Nat) (h : ∀ d ∈ f, d < 10) :
    renderFraction f = if f = [] then [] else ['.'] ++ f.map Rfc3339.Spec.digitChar := by
  cases f with
  | nil => rfl
  | cons d ds =>
    simp only [renderFraction, reduceCtorEq, ite_false, List.singleton_append, List.cons.injEq,
      true_and]
    apply List.map_congr_left
    intro x hx
    exact (digitChar_eq x (h x hx)).symm

theorem offset_render_eq (o : Offset) : o.render = Rfc3339.Spec.renderOffset o := by
  cases o <;> simp [Offset.render, Rfc3339.Spec.renderOffset, digits2]

theorem render_eq (t : Timestamp) (h : t.isValid = true) : t.render = Rfc3339.Spec.render t := by
  have hb := isValid_bounds h
  simp [Timestamp.render, Rfc3339.Spec.render, digits4, digits2, renderFraction_eq t.fraction hb.2.2.2.2.2.2.1,
    offset_render_eq]

/-! ## Parsing -/

theorem digitValue_digitChar (n : Nat) (h : n < 10) : digitValue (digitChar n) = some n := by
  have : ∀ i : Fin 10, digitValue (digitChar i.val) = some i.val := by decide
  exact this ⟨n, h⟩

theorem digitValue_some {c : Char} {v : Nat} (h : digitValue c = some v) :
    v < 10 ∧ digitChar v = c := by
  unfold digitValue at h
  split at h
  · rename_i hc
    simp only [le_iff_toNat] at hc
    have h0 : ('0' : Char).toNat = 48 := rfl
    have h9 : ('9' : Char).toNat = 57 := rfl
    rw [h0, h9] at hc
    injection h with h
    subst h
    refine ⟨by omega, ?_⟩
    unfold digitChar
    rw [Nat.sub_add_cancel hc.1]
    exact Char.ofNat_toNat c
  · simp at h

theorem two_pad2 (n : Nat) (h : n < 100) :
    two (digitChar (n / 10 % 10)) (digitChar (n % 10)) = some n := by
  simp [two, digitValue_digitChar, Nat.mod_lt]
  omega

theorem four_pad4 (n : Nat) (h : n < 10000) :
    four (digitChar (n / 1000 % 10)) (digitChar (n / 100 % 10)) (digitChar (n / 10 % 10))
      (digitChar (n % 10)) = some n := by
  simp [four, digitValue_digitChar, Nat.mod_lt]
  omega

theorem two_some {a b : Char} {n : Nat} (h : two a b = some n) : pad2 n = [a, b] := by
  simp only [two, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨x, hx, y, hy, h⟩ := h
  injection h with h
  subst h
  obtain ⟨hx1, hx2⟩ := digitValue_some hx
  obtain ⟨hy1, hy2⟩ := digitValue_some hy
  simp only [pad2]
  rw [show (10 * x + y) / 10 % 10 = x by omega, show (10 * x + y) % 10 = y by omega, hx2, hy2]

theorem four_some {a b c d : Char} {n : Nat} (h : four a b c d = some n) : pad4 n = [a, b, c, d] := by
  simp only [four, bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨w, hw, x, hx, y, hy, z, hz, h⟩ := h
  injection h with h
  subst h
  obtain ⟨hw1, hw2⟩ := digitValue_some hw
  obtain ⟨hx1, hx2⟩ := digitValue_some hx
  obtain ⟨hy1, hy2⟩ := digitValue_some hy
  obtain ⟨hz1, hz2⟩ := digitValue_some hz
  simp only [pad4]
  rw [show (1000 * w + 100 * x + 10 * y + z) / 1000 % 10 = w by omega,
    show (1000 * w + 100 * x + 10 * y + z) / 100 % 10 = x by omega,
    show (1000 * w + 100 * x + 10 * y + z) / 10 % 10 = y by omega,
    show (1000 * w + 100 * x + 10 * y + z) % 10 = z by omega, hw2, hx2, hy2, hz2]

/-- `takeDigits` splits its input: the digits it read, then the rest. -/
theorem takeDigits_spec (l : List Char) :
    l = (takeDigits l).1.map digitChar ++ (takeDigits l).2 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [takeDigits]
    split
    · rename_i v hv
      simp only [List.map_cons, List.cons_append]
      rw [(digitValue_some hv).2, ← ih]
    · rfl

theorem takeDigits_digits (ds : List Nat) (r : List Char) (hd : ∀ d ∈ ds, d < 10)
    (hr : takeDigits r = ([], r)) : takeDigits (ds.map digitChar ++ r) = (ds, r) := by
  induction ds with
  | nil => exact hr
  | cons d ds ih =>
    simp only [List.map_cons, List.cons_append, takeDigits]
    rw [digitValue_digitChar d (hd d (by simp))]
    simp only
    rw [ih (fun x hx => hd x (by simp [hx]))]

theorem takeDigits_offset (o : Offset) : takeDigits o.render = ([], o.render) := by
  cases o <;> rfl

/-- Whatever `parseFraction` reads is a rendered fraction. -/
theorem parseFraction_spec {l r : List Char} {ds : List Nat} (h : parseFraction l = some (ds, r)) :
    l = renderFraction ds ++ r := by
  unfold parseFraction at h
  split at h
  · rename_i cs
    simp only at h
    split at h
    · simp at h
    · rename_i hne
      injection h with h
      have hs := takeDigits_spec cs
      rw [h] at hs
      cases ds with
      | nil => rw [h] at hne; simp at hne
      | cons d ds => simp only [renderFraction, List.cons_append, ← hs]
  · injection h with h
    injection h with h1 h2
    subst h1 h2
    rfl

/-- The fraction digits stop at the offset, which never starts with a digit. -/
theorem parseFraction_render (f : List Nat) (o : Offset) (hf : ∀ d ∈ f, d < 10) :
    parseFraction (renderFraction f ++ o.render) = some (f, o.render) := by
  cases f with
  | nil => cases o <;> rfl
  | cons d ds =>
    simp only [renderFraction, List.cons_append, parseFraction]
    rw [takeDigits_digits (d :: ds) o.render hf (takeDigits_offset o)]
    rfl

theorem parseOffset_spec {l : List Char} {o : Offset} (h : parseOffset l = some o) : l = o.render := by
  unfold parseOffset at h
  split at h
  · injection h with h
    subst h
    rfl
  all_goals first
    | (simp at h; done)
    | simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨x, hx, y, hy, h⟩ := h
      injection h with h
      subst h
      simp only [Offset.render, two_some hx, two_some hy]
      rfl

theorem parseOffset_render (o : Offset) (h : o.isValid = true) : parseOffset o.render = some o := by
  cases o with
  | z => rfl
  | plus a b =>
    simp only [Offset.isValid, Bool.and_eq_true, decide_eq_true_eq] at h
    show parseOffset ['+', _, _, ':', _, _] = _
    simp only [parseOffset, two_pad2 a (by omega), two_pad2 b (by omega)]
    rfl
  | minus a b =>
    simp only [Offset.isValid, Bool.and_eq_true, decide_eq_true_eq] at h
    show parseOffset ['-', _, _, ':', _, _] = _
    simp only [parseOffset, two_pad2 a (by omega), two_pad2 b (by omega)]
    rfl

/-! ## The parser -/

theorem parseUpper_sound {u : List Char} {t : Timestamp} (h : parseUpper u = some t) :
    t.isValid = true ∧ u = t.render := by
  unfold parseUpper at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨year, hy, month, hm, day, hd, hour, hh, minute, hn, second, hs, ⟨f, r⟩, hr, offset, ho,
      hv⟩ := h
    simp only at hv
    split at hv
    · rename_i hval
      injection hv with hv
      subst hv
      refine ⟨hval, ?_⟩
      simp only at ho
      rw [parseFraction_spec hr, parseOffset_spec ho]
      simp only [Timestamp.render, four_some hy, two_some hm, two_some hd, two_some hh, two_some hn,
        two_some hs, List.cons_append, List.nil_append]
    · simp at hv
  · simp at h

theorem parseUpper_render {t : Timestamp} (h : t.isValid = true) : parseUpper t.render = some t := by
  obtain ⟨hy, hm, hd, hh, hn, hs, hf, ho⟩ := isValid_bounds h
  obtain ⟨year, month, day, hour, minute, second, fraction, offset⟩ := t
  simp only at hy hm hd hh hn hs hf ho
  simp only [Timestamp.render, pad4, pad2, List.cons_append, List.nil_append]
  rw [parseUpper.eq_1]
  simp only [four_pad4 year (by omega), two_pad2 month (by omega), two_pad2 day (by omega),
    two_pad2 hour (by omega), two_pad2 minute (by omega), two_pad2 second (by omega)]
  simp [parseFraction_render fraction offset hf, parseOffset_render offset ho, h]

theorem parseUpper_iff (u : List Char) (t : Timestamp) :
    parseUpper u = some t ↔ t.isValid = true ∧ u = t.render := by
  constructor
  · exact parseUpper_sound
  · rintro ⟨h, rfl⟩
    exact parseUpper_render h

theorem parse_iff' (s : String) (t : Timestamp) :
    parse s = some t ↔ t.isValid = true ∧ s.toList.map Rfc3339.Spec.asciiUpper = Rfc3339.Spec.render t := by
  have hmap : s.toList.map asciiUpper = s.toList.map Rfc3339.Spec.asciiUpper :=
    List.map_congr_left (fun c _ => asciiUpper_eq c)
  rw [parse, hmap, parseUpper_iff]
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, he.trans (render_eq t h)⟩
  · rintro ⟨h, he⟩
    exact ⟨h, he.trans (render_eq t h).symm⟩

end Rfc3339.Proofs.Format
