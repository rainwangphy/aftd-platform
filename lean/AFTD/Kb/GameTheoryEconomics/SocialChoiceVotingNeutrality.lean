import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPermuteCandidates
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPermuteWinners
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule

/-!
# SocialChoice.Voting.Neutrality

Topic: social_choice   Node: c31c6a6bdf9d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Neutrality`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Neutrality: relabeling candidates relabels the winner set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Neutrality: relabeling candidates relabels the winner set. -/
def SocialChoice.Voting.Neutrality (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (σ : Equiv.Perm A),
    permuteWinners σ (f P) = f (permuteCandidates P σ)
