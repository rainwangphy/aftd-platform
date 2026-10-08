import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallotPreserves
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallotTop
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingModifiedForwardProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallotXz
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefersAsymm
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersAsymm
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallotXy
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallotYz
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.modifiedForwardProfile_spec

Topic: social_choice   Node: 53dcfbe981c8

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.modifiedForwardProfile_spec`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.modifiedForwardProfile_spec
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.modifiedForwardProfile_spec [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hC : ∀ i ∈ C, Prefers P i x z) :
    ∀ i,
      (Prefers P i x z ↔ Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i x z) ∧
      (Prefers P i z x ↔ Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i z x) ∧
      (i ∈ C → Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i x y ∧
          Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y z) ∧
      (i ∉ C → Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y x ∧
          Prefers (modifiedForwardProfile P C x y z hxy hxz hyz) i y z) := by
  classical
  intro i
  by_cases hi : i ∈ C
  · simp [modifiedForwardProfile, hi, Prefers]
    constructor
    · constructor
      · intro _
        exact betweenBallot_xz (P.pref i) hxy hxz hyz
      · intro _
        exact hC i hi
    constructor
    · constructor
      · intro hzxi
        exact False.elim ((Prefers.asymm P i (hC i hi)) hzxi)
      · intro hzxi
        exact False.elim
          ((BallotPrefers.asymm _ (betweenBallot_xz (P.pref i) hxy hxz hyz)) hzxi)
    exact ⟨betweenBallot_xy (P.pref i) hxy hxz hyz,
      betweenBallot_yz (P.pref i) hxy hxz hyz⟩
  · have hx_ne_y : x ≠ y := hxy
    have hz_ne_y : z ≠ y := Ne.symm hyz
    simp [modifiedForwardProfile, hi, Prefers, topBallot_preserves, hx_ne_y, hz_ne_y,
      topBallot_top]
