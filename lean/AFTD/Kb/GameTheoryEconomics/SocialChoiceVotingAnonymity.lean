import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPermuteVoters
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.Anonymity

Topic: social_choice   Node: b1f2edd19048

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Anonymity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Anonymity: relabeling voters does not change the winner set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Anonymity: relabeling voters does not change the winner set. -/
def SocialChoice.Voting.Anonymity (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (σ : Equiv.Perm N), f (permuteVoters P σ) = f P
