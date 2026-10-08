import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPairSet
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripleSet

/-!
# SocialChoice.Voting.pair_subset_triple_right

Topic: social_choice   Node: 2d7b2d9065dc

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.pair_subset_triple_right`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.pair_subset_triple_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.pair_subset_triple_right (a b c : A) :
    pairSet a c ⊆ tripleSet a b c := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inr hx)
