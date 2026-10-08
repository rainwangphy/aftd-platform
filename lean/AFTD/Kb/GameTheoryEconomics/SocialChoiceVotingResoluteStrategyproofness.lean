import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResolute
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUpdateProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule

/-!
# SocialChoice.Voting.ResoluteStrategyproofness

Topic: social_choice   Node: 5908e589f0cb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.ResoluteStrategyproofness`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Strategyproofness for resolute rules: changing one ballot cannot produce a strictly better unique winner for the deviating voter.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Strategyproofness for resolute rules: changing one ballot cannot produce a strictly better unique winner for the deviating voter. -/
def SocialChoice.Voting.ResoluteStrategyproofness (f : VotingRule N A) (_hf : Resolute f) : Prop :=
  ∀ (P : Profile N A) (i : N) (r : LinearOrder A) (a b : A),
    f P = {a} →
    f (updateProfile P i r) = {b} →
    ¬ Prefers P i b a
