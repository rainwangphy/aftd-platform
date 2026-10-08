import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFDictatorial
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.F
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUnanimity

/-!
# SocialChoice.Voting.singleton_unanimity_dictatorial

Topic: social_choice   Node: ee9b902c2786

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.singleton_unanimity_dictatorial`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.singleton_unanimity_dictatorial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.singleton_unanimity_dictatorial [Fintype N] [Fintype A]
    [Subsingleton N] [Nonempty N] {F : SWF N A}
    (h : SWF.Unanimity F) : SWF.Dictatorial F := by
  refine ⟨(Classical.ofNonempty : N), ?_⟩
  intro P a b hab
  apply h
  intro j
  rw [← Subsingleton.allEq (Classical.ofNonempty : N) j]
  exact hab
