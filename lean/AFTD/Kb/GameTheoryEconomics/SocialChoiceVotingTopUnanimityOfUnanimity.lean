import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsTotal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.top_unanimity_of_unanimity

Topic: social_choice   Node: ead9ab2198b8

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.top_unanimity_of_unanimity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Top unanimity follows from weak-Pareto unanimity plus totality: if every voter ranks `a` first, then `a` is the unique winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Top unanimity follows from weak-Pareto unanimity plus totality: if every voter ranks `a` first, then `a` is the unique winner. -/
theorem SocialChoice.Voting.top_unanimity_of_unanimity [Nonempty A] {f : VotingRule N A}
    (hf : IsTotal f) (hU : Unanimity f) :
    ∀ (P : Profile N A) (a : A), (∀ i : N, TopRank P i a) → f P = {a} := by
  intro P a ha
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · by_contra hnot
    rcases hf P with ⟨b, hb⟩
    have hba : b = a := by
      by_contra hne
      exact hU P a b (fun i => ha i b hne) hb
    exact hnot (by simpa [hba] using hb)
  · intro b hb
    by_contra hne
    exact hU P a b (fun i => ha i b hne) hb
