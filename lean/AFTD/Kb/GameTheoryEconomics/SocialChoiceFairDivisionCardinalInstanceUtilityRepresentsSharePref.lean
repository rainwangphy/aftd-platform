import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.CardinalInstance.UtilityRepresentsSharePref

Topic: fair_division   Node: 40cb95ca3e81

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.UtilityRepresentsSharePref`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ordinal share instance is represented by a cardinal instance when its weak share preferences agree with the utility-induced weak order.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An ordinal share instance is represented by a cardinal instance when its weak share preferences agree with the utility-induced weak order. -/
def SocialChoice.FairDivision.CardinalInstance.UtilityRepresentsSharePref {N R S : Type*}
    (I₁ : ShareInstance N R S) (I₂ : CardinalInstance N R S) : Prop :=
  ∀ i s t, I₁.sharePref i s t ↔ I₂.utility i t ≤ I₂.utility i s
