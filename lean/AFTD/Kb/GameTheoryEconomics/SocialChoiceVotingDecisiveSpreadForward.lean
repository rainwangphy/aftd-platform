import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFIIA
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsWeaklyDecisiveFor
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisiveFor
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingModifiedForwardProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingModifiedForwardProfileSpec
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIiaStrict
import AFTD.Kb.GameTheoryEconomics.StrictTransitive
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.F

/-!
# SocialChoice.Voting.decisive_spread_forward

Topic: social_choice   Node: 7c5da3651fa1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.decisive_spread_forward`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.decisive_spread_forward
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.decisive_spread_forward [Fintype N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) (hIIA : SWF.IIA F)
    {C : Set N} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : IsWeaklyDecisiveFor F C x y) :
    IsDecisiveFor F C x z := by
  classical
  intro P hP
  let Q := modifiedForwardProfile P C x y z hxy hxz hyz
  have hQ := modifiedForwardProfile_spec P C hxy hxz hyz hP
  have hxz : ∀ i, Prefers P i x z ↔ Prefers Q i x z := fun i => (hQ i).1
  have hzx : ∀ i, Prefers P i z x ↔ Prefers Q i z x := fun i => (hQ i).2.1
  rw [iia_strict hIIA hxz hzx]
  exact strict_transitive (F Q).prop.transitive
    (h Q ⟨fun i hi => (hQ i).2.2.1 hi |>.1,
      fun i hi => (hQ i).2.2.2 hi |>.1⟩)
    (hU Q y z (fun i => by
      by_cases hi : i ∈ C
      · exact (hQ i).2.2.1 hi |>.2
      · exact (hQ i).2.2.2 hi |>.2))
