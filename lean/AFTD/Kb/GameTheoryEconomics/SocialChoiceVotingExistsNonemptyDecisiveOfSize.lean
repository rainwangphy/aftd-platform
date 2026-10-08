import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisive

/-!
# SocialChoice.Voting.exists_nonempty_decisive_of_size

Topic: social_choice   Node: 0f13d2aed19f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.exists_nonempty_decisive_of_size`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.exists_nonempty_decisive_of_size
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
def SocialChoice.Voting.exists_nonempty_decisive_of_size [Fintype N] [Fintype A]
    (F : SWF N A) (n : Nat) : Prop :=
  ∃ C : Set N, C.Nonempty ∧ IsDecisive F C ∧ C.ncard = n
