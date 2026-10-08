import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisiveFor
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.F

/-!
# SocialChoice.Voting.IsDecisive

Topic: social_choice   Node: d0bbc3221e35

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.IsDecisive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A coalition is decisive if it is decisive for every ordered pair of alternatives.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- A coalition is decisive if it is decisive for every ordered pair of alternatives. -/
def SocialChoice.Voting.IsDecisive [Fintype N] [Fintype A] (F : SWF N A) (C : Set N) : Prop :=
  ∀ a b, IsDecisiveFor F C a b
