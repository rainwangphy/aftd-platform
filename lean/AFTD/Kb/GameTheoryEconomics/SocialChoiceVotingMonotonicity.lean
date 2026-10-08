import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSimpleLift
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule

/-!
# SocialChoice.Voting.Monotonicity

Topic: social_choice   Node: 4e702e85ca19

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Monotonicity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Monotonicity: raising a selected alternative cannot make it unselected.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Monotonicity: raising a selected alternative cannot make it unselected. -/
def SocialChoice.Voting.Monotonicity (f : VotingRule N A) : Prop :=
  ∀ (P Q : Profile N A) (a : A), a ∈ f P → SimpleLift Q P a → a ∈ f Q
