import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.Weight

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation

Topic: fair_division   Node: 135a8b2889d5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift an additive valuation to an abstract `Valuation`. `(w.toValuation).val i S = Σ_{g ∈ S} w.weight i g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Lift an additive valuation to an abstract `Valuation`. `(w.toValuation).val i S = Σ_{g ∈ S} w.weight i g`. -/
def SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation (w : AdditiveValuation N G) : Valuation N G :=
  ⟨fun i S => ∑ g ∈ S, w.weight i g⟩
