import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopChoice

/-!
# SocialChoice.Voting.Dictatorial

Topic: social_choice   Node: 861e023c5faf

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Dictatorial`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A rule is dictatorial if one voter always gets their top-ranked alternative as the unique winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- A rule is dictatorial if one voter always gets their top-ranked alternative as the unique winner. -/
def SocialChoice.Voting.Dictatorial [Nonempty A] (f : VotingRule N A) : Prop :=
  ∃ i : N, ∀ P : Profile N A, f P = {topChoice P i}
