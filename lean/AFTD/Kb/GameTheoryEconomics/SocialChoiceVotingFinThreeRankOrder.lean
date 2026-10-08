import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.finThreeRankOrder

Topic: social_choice   Node: 0de0f5e1eab1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.finThreeRankOrder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.finThreeRankOrder
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.finThreeRankOrder
    (r : Fin 3 → Nat) (hr : Function.Injective r) : LinearOrder (Fin 3) :=
  ballotFromInjective (inferInstance : LinearOrder Nat) r hr
