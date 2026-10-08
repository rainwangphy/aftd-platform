import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResolute
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResoluteStrategyproofness
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMonotonicity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSimpleLift
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingHybridProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingStrategyproofInsertPreservesChoice
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.strategyproof_monotonic

Topic: social_choice   Node: dcff8df7238c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.strategyproof_monotonic`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Strategy-proofness implies monotonicity for finite voter sets. [MSZ 21.35]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- Strategy-proofness implies monotonicity for finite voter sets. [MSZ 21.35] -/
theorem SocialChoice.Voting.strategyproof_monotonic [Fintype N] [Fintype A]
    (f : VotingRule N A) (hf_res : Resolute f)
    (hSP : ResoluteStrategyproofness f hf_res) :
    Monotonicity f := by
  classical
  intro P Q a ha hLift
  have hAll : ∀ S : Finset N, a ∈ f (hybridProfile P Q S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [hybridProfile] using ha
    | insert i S hi ih =>
        exact strategyproof_insert_preserves_choice f hf_res hSP hLift hi ih
  simpa [hybridProfile] using hAll (Finset.univ : Finset N)
