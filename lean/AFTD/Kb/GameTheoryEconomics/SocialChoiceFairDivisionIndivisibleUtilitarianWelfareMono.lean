import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleUtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareMono
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Indivisible.utilitarianWelfare_mono

Topic: fair_division   Node: b0b8076b4409

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.utilitarianWelfare_mono`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/SocialWelfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian welfare is monotone: pointwise improvement implies welfare improvement. The valuation codomain is fixed to `ℝ`, so no ordered-algebra assumptions are needed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
variable [Fintype N] in
/-- Utilitarian welfare is monotone: pointwise improvement implies welfare improvement. The valuation codomain is fixed to `ℝ`, so no ordered-algebra assumptions are needed. -/
lemma SocialChoice.FairDivision.Indivisible.utilitarianWelfare_mono
    (v : Valuation N G) (A B : Allocation N G)
    (h : ∀ i : N, v.val i (A i) ≤ v.val i (B i)) :
    utilitarianWelfare v A ≤ utilitarianWelfare v B :=
  SocialChoice.FairDivision.utilitarianWelfare_mono v.val A B h
