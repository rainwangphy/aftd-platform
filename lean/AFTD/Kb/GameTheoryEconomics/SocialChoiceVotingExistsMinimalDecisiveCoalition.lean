import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingExistsNonemptyDecisiveOfSize
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUnanimityUnivIsDecisive
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisive

/-!
# SocialChoice.Voting.exists_minimal_decisive_coalition

Topic: social_choice   Node: 9524a1ef8a96

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.exists_minimal_decisive_coalition`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.exists_minimal_decisive_coalition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.exists_minimal_decisive_coalition [Fintype N] [Nonempty N] [Fintype A]
    {F : SWF N A} (hU : SWF.Unanimity F) :
    ∃ n, Minimal (exists_nonempty_decisive_of_size F) n := by
  classical
  apply exists_minimal_of_wellFoundedLT
  refine ⟨Fintype.card N, Set.univ, ?_, ?_, ?_⟩
  · exact ⟨Classical.ofNonempty, trivial⟩
  · exact unanimity_univ_isDecisive hU
  · simp [Set.ncard_univ, Nat.card_eq_fintype_card]
