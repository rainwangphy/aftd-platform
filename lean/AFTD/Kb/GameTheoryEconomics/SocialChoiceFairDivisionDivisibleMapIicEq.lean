import AFTD.Prelude

/-!
# SocialChoice.FairDivision.Divisible.map_Iic_eq

Topic: fair_division   Node: 26956e330a63

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.map_Iic_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/DubinsSpanier.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.FairDivision.Divisible.map_Iic_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
lemma SocialChoice.FairDivision.Divisible.map_Iic_eq (μ : Measure I) (t : I) :
    (μ.map Subtype.val) (Set.Iic (t : ℝ)) = μ (Set.Iic t) := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  rfl
