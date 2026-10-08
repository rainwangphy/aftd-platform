import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMajorityPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.CondorcetWinner

Topic: social_choice   Node: 5107258e59e6

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.CondorcetWinner`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`a` is a Condorcet winner if it beats every other alternative by strict pairwise majority.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- `a` is a Condorcet winner if it beats every other alternative by strict pairwise majority. -/
def SocialChoice.Voting.CondorcetWinner [Fintype N] [Fintype A] (P : Profile N A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → MajorityPrefers P a b
