import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRankInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.betweenKey_injective

Topic: social_choice   Node: 423322740561

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.betweenKey_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.betweenKey_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.betweenKey_injective [Fintype A] (r : LinearOrder A)
    {x y z : A} (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (betweenKey r x y z) := by
  classical
  intro a b h
  unfold betweenKey at h
  by_cases hax : a = x <;> by_cases hbx : b = x
  · simp_all
  · by_cases hby : b = y <;> by_cases hbz : b = z <;> simp_all
  · by_cases hay : a = y <;> by_cases haz : a = z <;> simp_all
  · by_cases hay : a = y <;> by_cases hby : b = y
    · simp_all
    · by_cases hbz : b = z <;> simp_all
    · by_cases haz : a = z <;> simp_all
    · by_cases haz : a = z <;> by_cases hbz : b = z
      · simp_all
      · simp_all
      · simp_all
      · simp_all
        exact rank_injective r (by omega)
