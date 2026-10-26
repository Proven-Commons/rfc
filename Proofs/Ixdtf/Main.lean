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

theorem Spec.ixdtf_vectors :
    (parseExt "1996-12-19T16:39:57-08:00[America/Los_Angeles][u-ca=hebrew]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩,
        some (false, .name ["America".toList, "Los_Angeles".toList]),
        [⟨false, "u-ca".toList, ["hebrew".toList]⟩]⟩) ∧
    (parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]" =
      some ⟨⟨1996, 12, 19, 16, 39, 57, [], .minus 8 0⟩, none,
        [⟨false, "_foo".toList, ["bar".toList]⟩, ⟨false, "_baz".toList, ["bat".toList]⟩]⟩) ∧
    -- Elective: an inconsistent zone, an unknown key, repeated keys
    ((parseExt "2022-07-08T00:14:07+01:00[Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07+01:00[knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][u-ca=japanese]").bind (·.lookup "u-ca".toList) =
      some ⟨false, "u-ca".toList, ["chinese".toList]⟩) ∧
    -- Critical: the four of section 3.3
    ((parseExt "2022-07-08T00:14:07+01:00[!Europe/Paris]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!u-ca=chinese][u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[u-ca=chinese][!u-ca=japanese]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    ((parseExt "2022-07-08T00:14:07Z[!knort=blargel]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    -- Figures 1 and 2 of section 3.4
    ((parseExt "2022-07-08T00:14:07+00:00[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some true) ∧
    ((parseExt "2022-07-08T00:14:07+00:00[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[!Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    ((parseExt "2022-07-08T00:14:07Z[Europe/London]").map (·.erroneous Spec.exampleProcessor) =
      some false) ∧
    -- An experiment the application does not take part in
    ((parseExt "1996-12-19T16:39:57-08:00[_foo=bar][_baz=bat]").map
      (·.erroneous Spec.exampleProcessor) = some true) ∧
    -- Refused by the grammar: an empty item, `.` and `..`, an upper case
    -- key, an empty value, a time zone after a tag, `Z` as an offset
    -- (it reads as a zone name), an offset out of range
    parseExt "2022-07-08T00:14:07Z[]" = none ∧
    parseExt "2022-07-08T00:14:07Z[.]" = none ∧
    parseExt "2022-07-08T00:14:07Z[a/..]" = none ∧
    parseExt "2022-07-08T00:14:07Z[U-ca=x]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=a--b]" = none ∧
    parseExt "2022-07-08T00:14:07Z[u-ca=x][Europe/Paris]" = none ∧
    parseExt "2022-07-08T00:14:07Z[+24:00]" = none := by
  and_intros <;> decide +kernel
