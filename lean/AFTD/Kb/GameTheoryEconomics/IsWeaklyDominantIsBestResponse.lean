import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsBestResponse
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateSelf

/-!
# IsWeaklyDominant.isBestResponse

Topic: equilibria   Node: 090be178f698

Provenance: formalization of a published result. Source: EconCSLib, `IsWeaklyDominant.isBestResponse`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Dominance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

T2: A weakly dominant strategy is a best response to any profile where player `i` plays it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- T2: A weakly dominant strategy is a best response to any profile where player `i` plays it. -/
theorem IsWeaklyDominant.isBestResponse {G : EconCSLib.StrategicGame N U} {i : N} {s : G.strategy i}
    (hdom : IsWeaklyDominant G i s) (σ : G.Profile) (hσ : σ i = s) :
    IsBestResponse G σ i := by
  intro s'
  have h := hdom s' σ
  simp only [← hσ, Profile.deviate_self] at h
  exact h
