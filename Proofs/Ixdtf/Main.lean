/-
  The IXDTF statements of `Spec.lean`, under the same names, from the
  lemmas in the other files of `Proofs/Ixdtf/`. The test vectors are
  checked by evaluation.
-/

import Proofs.Ixdtf.Parse
import Proofs.Ixdtf.Rules

open Rfc3339

theorem Spec.parseExt_iff (s : String) (e : Ext) :
    parseExt s = some e ↔
      Spec.ExtValid e ∧ ∃ dt, s.toList = dt ++ Spec.renderSuffix e ∧
        dt.map Spec.asciiUpper = Spec.render e.stamp :=
  Rfc3339.Proofs.Ixdtf.parseExt_iff s e

theorem Spec.printExt_eq (e : Ext) (h : Spec.ExtValid e) :
    e.print.toList = Spec.render e.stamp ++ Spec.renderSuffix e :=
  Rfc3339.Proofs.Ixdtf.printExt_eq e h

theorem Spec.parseExt_print (e : Ext) (h : Spec.ExtValid e) : parseExt e.print = some e :=
  Rfc3339.Proofs.Ixdtf.parseExt_print e h

theorem Spec.parseExt_plain (s : String) (h : '[' ∉ s.toList) :
    parseExt s = (parse s).map fun t => ⟨t, none, []⟩ :=
  Rfc3339.Proofs.Ixdtf.parseExt_plain s h

theorem Spec.lookup_iff (e : Ext) (k : List Char) (t : Tag) :
    e.lookup k = some t ↔ ∃ l r, e.tags = l ++ t :: r ∧ t.key = k ∧ ∀ u ∈ l, u.key ≠ k :=
  Rfc3339.Proofs.Ixdtf.lookup_iff e k t

theorem Spec.erroneous_iff (p : Processor) (e : Ext) :
    e.erroneous p = true ↔ Spec.MustReject p e :=
  Rfc3339.Proofs.Ixdtf.erroneous_iff p e

/-- The grammar's checks on an IXDTF timestamp, made by the code's own
    functions, which the lemmas of `Proofs/Ixdtf/Suffix.lean` tie to the
    spec. Used to check the test vectors that read a string without
    running the whole parser in the kernel, which one of the external
    kernels cannot do in its stack on the long ones. Every vector of
    `Spec.ixdtf_vectors` that reads a string goes this way, through
    `vx_parseExt`, short or long. The kernel runs `parseExt` only on the
    nine strings the grammar refuses, of at most 42 characters. -/
def vx_validB (e : Ext) : Bool :=
  e.stamp.isValid &&
  (match e.zone with
   | some (_, .name parts) => !parts.isEmpty && parts.all zonePartOK
   | some (_, .offset o) => o != .z && o.isValid
   | none => true) &&
  e.tags.all (fun t => keyOK t.key && !t.values.isEmpty && t.values.all valueOK)

theorem vx_validB_sound (e : Ext) (h : vx_validB e = true) : Spec.ExtValid e := by
  obtain ⟨stamp, zone, tags⟩ := e
  simp only [vx_validB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hs, hz⟩, ht⟩ := h
  refine ⟨(Rfc3339.Proofs.Valid.isValid_iff stamp).mp hs, ?_, ?_⟩
  · intro c z hcz
    subst hcz
    cases z with
    | name parts =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at hz
      exact ⟨hz.1, fun p hp => (Rfc3339.Proofs.Ixdtf.sx_zonePartOK_iff p).mp (hz.2 p hp)⟩
    | offset o =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
      exact ⟨hz.1, (Rfc3339.Proofs.Valid.offset_isValid_iff o).mp hz.2⟩
  · intro t htm
    have h3 := ht t htm
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at h3
    exact ⟨(Rfc3339.Proofs.Ixdtf.sx_keyOK_iff _).mp h3.1.1, h3.1.2,
      fun v hv => (Rfc3339.Proofs.Ixdtf.sx_valueOK_iff v).mp (h3.2 v hv)⟩

theorem vx_parseExt (s : String) (e : Ext) (dt : List Char) (hv : vx_validB e = true)
    (hs : s.toList = dt ++ Spec.renderSuffix e) (hd : dt.map Spec.asciiUpper = Spec.render e.stamp) :
    parseExt s = some e :=
  (Rfc3339.Proofs.Ixdtf.parseExt_iff s e).2 ⟨vx_validB_sound e hv, dt, hs, hd⟩

/-- The timestamps of RFC 9557 in sections 1.2, 3.3, 3.4 and 4.2, with
    the application of `Spec.exampleProcessor`. Two of them, both with
    no suffix, are not here: `2022-07-08T00:14:07+01:00`, which section
    3.3 says its first example can be treated as, and
    `1996-12-20T00:39:57Z`, the instant of Figure 4 in UTC. Section 1.2
    gives two with no seconds, and the grammar refuses them: RFC 3339,
    section 5.6, makes `time-second` part of `partial-time`, which
    `date-time` requires. Section 5.6 has
    `date-time = full-date "T" full-time`,
    `full-time = partial-time time-offset` and
    `partial-time = time-hour ":" time-minute ":" time-second [time-secfrac]`.
    Each of the others is read, and is erroneous exactly where the RFC
    says it must be treated so. Also critical time zones that agree with
    the offset, a critical `-00:00` zone that does not, two strings
    judged by the application of `Spec.secondProcessor`, and other
    strings the grammar refuses. -/
theorem Spec.ixdtf_vectors :
    -- Section 4.2, Figures 4 to 7
    parseExt "1996-12-19T16:39:57-08:00" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none, []⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]), []⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]),
        [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩ ∧
    parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none,
        [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩ ∧
    ((parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    ((parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    -- An experiment the application does not take part in
    ((parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    -- Section 1.2: an offset time zone
    parseExt "2022-07-08T00:14:07+08:45[+08:45]" =
      some ⟨⟨2022, 7, 8, 0, 14, 7, [], .plus 8 45⟩, some (false, .offset (.plus 8 45)), []⟩ ∧
    ((parseExt "2022-07-08T00:14:07+08:45[!+08:45]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    -- Section 1.2: the two strings with no seconds, which the grammar
    -- refuses
    parseExt "2020-01-01T00:00+01:00[Europe/Paris]" = none ∧
    parseExt "2020-01-01T00:00+01:00[+01:00]" = none ∧
    -- Section 3.3, elective: an inconsistent zone, the zones of the note,
    -- an unknown key, repeated keys
    ((parseExt "2022-07-08T00:14:07+01:00[Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T02:14:07+02:00[Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07+01:00[knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    -- Section 3.3, critical: the four examples
    ((parseExt "2022-07-08T00:14:07+01:00[!Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    -- Section 3.4, Figures 1 and 2
    ((parseExt "2022-07-08T00:14:07+00:00[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07+00:00[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    -- Critical zones that agree with the offset, and a critical `-00:00`
    -- zone, offset 0, under an offset of +01:00
    ((parseExt "1996-12-19T16:39:57-08:00[!America/Los_Angeles]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T02:14:07+02:00[!Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T01:14:07+01:00[!-00:00]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    -- `Z` in brackets is a zone name, not an offset
    ((parseExt "2022-07-08T00:14:07Z[Z]").map (·.zone) = some (some (false, .name ["Z".toList]))) ∧
    -- A second application, with other tags: a critical calendar the
    -- first does not process, with an elective tag of the experiment it
    -- takes part in; then a critical tag of that experiment whose value
    -- it cannot process
    ((parseExt "2022-07-08T00:14:07Z[!u-ca=coptic][_x=b]").map
      (·.erroneous Spec.secondProcessor) = some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[!_x=b]").map (·.erroneous Spec.secondProcessor) =
      some true) ∧
    -- Refused by the grammar: an empty item, `.` and `..`, an upper case
    -- key, an empty value, a time zone after a tag, an offset out of range
    parseExt "2022-07-08T00:14:07Z[]" = none ∧
    parseExt "2022-07-08T00:14:07Z[.]" = none ∧
    parseExt "2022-07-08T00:14:07Z[a/..]" = none ∧
    parseExt "2022-07-08T00:14:07Z[U-ca=x]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=a--b]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=x][Europe/Paris]" = none ∧
    parseExt "2022-07-08T00:14:07Z[+24:00]" = none := by
  and_intros
  · exact vx_parseExt "1996-12-19T16:39:57-08:00" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, none, []⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact vx_parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, some (false, .name ["America".toList, "Los_Angeles".toList]), []⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact vx_parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, some (false, .name ["America".toList, "Los_Angeles".toList]), [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact vx_parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, none, [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · rw [vx_parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, some (false, .name ["America".toList, "Los_Angeles".toList]), []⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, some (false, .name ["America".toList, "Los_Angeles".toList]), [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, none, [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · exact vx_parseExt "2022-07-08T00:14:07+08:45[+08:45]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 8 45)⟩, some (false, .offset (.plus 8 45)), []⟩
        "2022-07-08T00:14:07+08:45".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · rw [vx_parseExt "2022-07-08T00:14:07+08:45[!+08:45]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 8 45)⟩, some (true, .offset (.plus 8 45)), []⟩
        "2022-07-08T00:14:07+08:45".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07+01:00[Europe/Paris]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 1 0)⟩, some (false, .name ["Europe".toList, "Paris".toList]), []⟩
        "2022-07-08T00:14:07+01:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[Europe/Paris]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, some (false, .name ["Europe".toList, "Paris".toList]), []⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T02:14:07+02:00[Europe/Paris]" ⟨⟨2022, 7, 8, 2, 14, 7, [], (.plus 2 0)⟩, some (false, .name ["Europe".toList, "Paris".toList]), []⟩
        "2022-07-08T02:14:07+02:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07+01:00[knort=blargel]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 1 0)⟩, none, [⟨false, "knort".toList, ["blargel".toList]⟩]⟩
        "2022-07-08T00:14:07+01:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨false, "u-ca".toList, ["chinese".toList]⟩, ⟨false, "u-ca".toList, ["japanese".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨false, "u-ca".toList, ["chinese".toList]⟩, ⟨false, "u-ca".toList, ["japanese".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[u-ca=chinese]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨false, "u-ca".toList, ["chinese".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07+01:00[!Europe/Paris]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 1 0)⟩, some (true, .name ["Europe".toList, "Paris".toList]), []⟩
        "2022-07-08T00:14:07+01:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨true, "u-ca".toList, ["chinese".toList]⟩, ⟨false, "u-ca".toList, ["japanese".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨false, "u-ca".toList, ["chinese".toList]⟩, ⟨true, "u-ca".toList, ["japanese".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[!knort=blargel]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨true, "knort".toList, ["blargel".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07+00:00[!Europe/London]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 0 0)⟩, some (true, .name ["Europe".toList, "London".toList]), []⟩
        "2022-07-08T00:14:07+00:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07+00:00[Europe/London]" ⟨⟨2022, 7, 8, 0, 14, 7, [], (.plus 0 0)⟩, some (false, .name ["Europe".toList, "London".toList]), []⟩
        "2022-07-08T00:14:07+00:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[!Europe/London]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, some (true, .name ["Europe".toList, "London".toList]), []⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[Europe/London]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, some (false, .name ["Europe".toList, "London".toList]), []⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "1996-12-19T16:39:57-08:00[!America/Los_Angeles]" ⟨⟨1996, 12, 19, 16, 39, 57, [], (.minus 8 0)⟩, some (true, .name ["America".toList, "Los_Angeles".toList]), []⟩
        "1996-12-19T16:39:57-08:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T02:14:07+02:00[!Europe/Paris]" ⟨⟨2022, 7, 8, 2, 14, 7, [], (.plus 2 0)⟩, some (true, .name ["Europe".toList, "Paris".toList]), []⟩
        "2022-07-08T02:14:07+02:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T01:14:07+01:00[!-00:00]" ⟨⟨2022, 7, 8, 1, 14, 7, [], (.plus 1 0)⟩, some (true, .offset (.minus 0 0)), []⟩
        "2022-07-08T01:14:07+01:00".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[Z]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, some (false, .name ["Z".toList]), []⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[!u-ca=coptic][_x=b]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨true, "u-ca".toList, ["coptic".toList]⟩, ⟨false, "_x".toList, ["b".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [vx_parseExt "2022-07-08T00:14:07Z[!_x=b]" ⟨⟨2022, 7, 8, 0, 14, 7, [], .z⟩, none, [⟨true, "_x".toList, ["b".toList]⟩]⟩
        "2022-07-08T00:14:07Z".toList (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
