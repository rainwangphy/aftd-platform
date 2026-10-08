import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResolute
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefersTotalOfNe
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResoluteStrategyproofness
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUpdateProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSimpleLift
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingHybridProfileEraseEqUpdate
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingHybridProfileInsertEqUpdate
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingHybridProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingResoluteEqSingletonOfMem

/-!
# SocialChoice.Voting.strategyproof_insert_preserves_choice

Topic: social_choice   Node: 5816f5bc1e52

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.strategyproof_insert_preserves_choice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.strategyproof_insert_preserves_choice
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.strategyproof_insert_preserves_choice [Fintype N] [DecidableEq N] [Fintype A]
    (f : VotingRule N A) (hf_res : Resolute f)
    (hSP : ResoluteStrategyproofness f hf_res)
    {P Q : Profile N A} {a : A} (hLift : SimpleLift Q P a)
    {S : Finset N} {i : N} (hi : i ∉ S)
    (ha : a ∈ f (hybridProfile P Q S)) :
    a ∈ f (hybridProfile P Q (insert i S)) := by
  classical
  by_contra hnot
  let H0 := hybridProfile P Q S
  let H1 := hybridProfile P Q (insert i S)
  have hf0 : f H0 = {a} := resolute_eq_singleton_of_mem hf_res ha
  rcases Finset.card_eq_one.mp (hf_res H1) with ⟨b, hb⟩
  have hbmem : b ∈ f H1 := by simp [hb]
  have hba : b ≠ a := by
    intro h
    exact hnot (by simpa [h] using hbmem)
  have hforward : ¬ Prefers H0 i b a := by
    have hupdate : f (updateProfile H0 i (Q.pref i)) = {b} := by
      rw [← hybridProfile_insert_eq_update P Q S hi]
      exact hb
    exact hSP H0 i (Q.pref i) a b hf0 hupdate
  have hreverse : ¬ Prefers H1 i a b := by
    have hupdate : f (updateProfile H1 i (P.pref i)) = {a} := by
      rw [← hybridProfile_erase_eq_update P Q S hi]
      exact hf0
    exact hSP H1 i (P.pref i) b a hb hupdate
  have hP_or := Prefers.total_of_ne P i (Ne.symm hba)
  cases hP_or with
  | inl hPab =>
      have hQab := (hLift i b).left hPab
      have hH1ab : Prefers H1 i a b := by
        simpa [H1, hybridProfile, Prefers] using hQab
      exact hreverse hH1ab
  | inr hPba =>
      have hH0ba : Prefers H0 i b a := by
        simpa [H0, hybridProfile, Prefers, hi] using hPba
      exact hforward hH0ba
