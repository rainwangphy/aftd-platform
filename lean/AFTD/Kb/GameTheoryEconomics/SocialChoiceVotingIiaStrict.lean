import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFIIA
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# SocialChoice.Voting.iia_strict

Topic: social_choice   Node: 37628192cd2a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.iia_strict`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.iia_strict
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.iia_strict [Fintype N] [Fintype A] {F : SWF N A} (hF : SWF.IIA F)
    {P Q : Profile N A} {a b : A}
    (hab : ∀ i, Prefers P i a b ↔ Prefers Q i a b)
    (hba : ∀ i, Prefers P i b a ↔ Prefers Q i b a) :
    strict (F P) a b ↔ strict (F Q) a b := by
  simp [strict, hF P Q a b hab, hF P Q b a hba]
