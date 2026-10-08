import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# SocialChoice.Voting.IsDecisiveFor

Topic: social_choice   Node: ecbf17e8796b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.IsDecisiveFor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A coalition is decisive for `a` over `b` if unanimous strict support inside the coalition forces the social strict preference `a ≻ b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- A coalition is decisive for `a` over `b` if unanimous strict support inside the coalition forces the social strict preference `a ≻ b`. -/
def SocialChoice.Voting.IsDecisiveFor [Fintype N] [Fintype A]
    (F : SWF N A) (C : Set N) (a b : A) : Prop :=
  ∀ P : Profile N A, (∀ i ∈ C, Prefers P i a b) → strict (F P) a b
