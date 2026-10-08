import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.Unanimity

Topic: social_choice   Node: 82439d2c8e12

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Unanimity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unanimity/Pareto for set-valued voting rules: no unanimously dominated alternative is selected.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Unanimity/Pareto for set-valued voting rules: no unanimously dominated alternative is selected. -/
def SocialChoice.Voting.Unanimity (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (a b : A), (∀ i : N, Prefers P i a b) → b ∉ f P
