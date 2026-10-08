import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingCondorcetWinner
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule

/-!
# SocialChoice.Voting.CondorcetConsistency

Topic: social_choice   Node: acb70ac1147a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.CondorcetConsistency`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A rule is Condorcet-consistent if every Condorcet winner is the unique winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- A rule is Condorcet-consistent if every Condorcet winner is the unique winner. -/
def SocialChoice.Voting.CondorcetConsistency [Fintype N] [Fintype A] (f : VotingRule N A) : Prop :=
  ∀ (P : Profile N A) (a : A), CondorcetWinner P a → f P = {a}
