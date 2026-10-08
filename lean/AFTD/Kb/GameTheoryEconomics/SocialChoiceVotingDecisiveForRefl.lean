import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefersAsymm
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisiveFor
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# SocialChoice.Voting.decisive_for_refl

Topic: social_choice   Node: bdd2ff7bce3d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.decisive_for_refl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.decisive_for_refl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.decisive_for_refl [Fintype N] [Fintype A]
    {F : SWF N A} {C : Set N} (hC : Set.Nonempty C) (x : A) :
    IsDecisiveFor F C x x := by
  intro P hP
  rcases hC with ⟨i, hi⟩
  exact False.elim ((Prefers.asymm P i (hP i hi)) (hP i hi))
