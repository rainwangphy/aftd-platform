import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.rank_lt_of_lt

Topic: social_choice   Node: 30ddfadba2ce

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.rank_lt_of_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.rank_lt_of_lt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
theorem SocialChoice.Voting.rank_lt_of_lt [Fintype A] (r : LinearOrder A) {a b : A} (hab : BallotPrefers r a b) :
    rank r a < rank r b := by
  classical
  letI := r
  change a < b at hab
  have hsubset :
      (Finset.univ.filter (fun x : A => BallotPrefers r x a)) ⊆
        (Finset.univ.filter (fun x : A => BallotPrefers r x b)) := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨by simp, by
        change x < b
        exact lt_trans (by simpa [BallotPrefers] using (Finset.mem_filter.mp hx).2) hab⟩
  have hssub :
      (Finset.univ.filter (fun x : A => BallotPrefers r x a)) ⊂
        (Finset.univ.filter (fun x : A => BallotPrefers r x b)) := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨a, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, by simpa [BallotPrefers] using hab⟩
    · intro ha
      exact lt_irrefl a (by simpa [BallotPrefers] using (Finset.mem_filter.mp ha).2)
  simpa [rank] using Finset.card_lt_card hssub
