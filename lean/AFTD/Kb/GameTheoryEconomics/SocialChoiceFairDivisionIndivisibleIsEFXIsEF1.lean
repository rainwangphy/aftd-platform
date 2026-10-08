import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEFX
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.Tcs.G

/-!
# SocialChoice.FairDivision.Indivisible.IsEFX.isEF1

Topic: fair_division   Node: 933e01127945

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsEFX.isEF1`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EFX implies EF1: the universal witness in EFX is in particular an existential witness for EF1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [DecidableEq G] in
/-- EFX implies EF1: the universal witness in EFX is in particular an existential witness for EF1. -/
theorem SocialChoice.FairDivision.Indivisible.IsEFX.isEF1 (v : Valuation N G) (A : Allocation N G)
    (h : IsEFX v A) : IsEF1 v A := fun i j hij ⟨g, hg⟩ => ⟨g, hg, h i j hij g hg⟩
