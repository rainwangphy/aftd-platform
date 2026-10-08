import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRankInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.topKey_injective

Topic: social_choice   Node: db547c3e6018

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topKey_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topKey_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.topKey_injective [Fintype A] (r : LinearOrder A) (y : A) :
    Function.Injective (topKey r y) := by
  classical
  intro a b h
  unfold topKey at h
  by_cases hay : a = y <;> by_cases hby : b = y
  · simp_all
  · simp_all
  · simp_all
  · simp_all
    exact rank_injective r (by omega)
