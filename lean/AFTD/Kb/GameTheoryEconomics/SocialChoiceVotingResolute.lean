import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.Resolute

Topic: social_choice   Node: 05b9c8130717

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Resolute`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A voting rule is resolute if it always returns exactly one winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A voting rule is resolute if it always returns exactly one winner. -/
def SocialChoice.Voting.Resolute [Fintype N] [Fintype A] (f : VotingRule N A) : Prop :=
  ∀ P : Profile N A, Finset.card (f P) = 1
