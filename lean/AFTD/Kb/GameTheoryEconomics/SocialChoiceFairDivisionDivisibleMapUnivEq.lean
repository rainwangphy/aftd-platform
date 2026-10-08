import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Divisible.map_univ_eq

Topic: fair_division   Node: dfac7d7c308a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.map_univ_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/DubinsSpanier.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.FairDivision.Divisible.map_univ_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
lemma SocialChoice.FairDivision.Divisible.map_univ_eq (μ : Measure I) :
    (μ.map Subtype.val) Set.univ = μ Set.univ := by
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp
