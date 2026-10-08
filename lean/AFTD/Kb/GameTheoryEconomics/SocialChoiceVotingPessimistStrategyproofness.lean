import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUpdateProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.PessimistStrategyproofness

Topic: social_choice   Node: 1c65b6c66e0e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.PessimistStrategyproofness`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pessimist strategyproofness for set-valued rules.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Pessimist strategyproofness for set-valued rules. -/
def SocialChoice.Voting.PessimistStrategyproofness (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (i : N) (r : LinearOrder A),
    ¬ ∃ a ∈ f P, ∀ b ∈ f (updateProfile P i r), Prefers P i b a
