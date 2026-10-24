import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasFractionalMatching
import AFTD.Kb.GameTheoryEconomics.RankScoreCandidateWeight

/-!
# is_rank_score_veto_core

Topic: social_choice   Node: 990cd393931d

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 2, Section 2.3

Given a nonempty finite voter type V, a finite candidate type C with decidable equality, a scoring vector s : Fin (Fintype.card C) → ℚ, an election profile prof : V → LinearOrder C, and a candidate a in C, is_rank_score_veto_core s prof a asserts that has_fractional_matching prof (fun _ => 1 / (Fintype.card V : ℝ)) (fun c => ((rank_score_candidate_weight s prof c : ℚ) : ℝ)) a.
-/

/-- Membership of candidate a in the (p^unif, q^s)-veto core. -/
def is_rank_score_veto_core {V C : Type*} [Fintype V] [Nonempty V] [Fintype C] [DecidableEq C]
    (s : Fin (Fintype.card C) → ℚ) (prof : V → LinearOrder C) (a : C) : Prop :=
  has_fractional_matching prof
    (fun _ => 1 / (Fintype.card V : ℝ))
    (fun c => ((rank_score_candidate_weight s prof c : ℚ) : ℝ))
    a
