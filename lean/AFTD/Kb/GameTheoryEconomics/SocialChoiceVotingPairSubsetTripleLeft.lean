import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPairSet
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripleSet

/-!
# SocialChoice.Voting.pair_subset_triple_left

Topic: social_choice   Node: ba1f17dad923

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.pair_subset_triple_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.pair_subset_triple_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.pair_subset_triple_left (a b c : A) :
    pairSet a b ⊆ tripleSet a b c := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
