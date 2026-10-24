import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateRank
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne

/-!
# rank_score_candidate_weight

Topic: social_choice   Node: 250d451792ff

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 2

Given a nonempty finite type of voters V, a finite type of candidates C with decidable equality, a scoring function s : Fin (Fintype.card C) → ℚ, a profile prof : V → LinearOrder C, and a candidate c : C, rank_score_candidate_weight s prof c is the sum over all voters v in V of s applied to candidate_rank (prof v) c, divided by the product of the number of voters (Fintype.card V : ℚ) and scoring_norm_one s.
-/

/-- Normalized candidate weight under scoring vector s and preference profile prof. -/
def rank_score_candidate_weight {V C : Type*} [Fintype V] [Nonempty V] [Fintype C] [DecidableEq C]
    (s : Fin (Fintype.card C) → ℚ) (prof : V → LinearOrder C) (c : C) : ℚ :=
  (∑ v : V, s (candidate_rank (prof v) c)) /
    ((Fintype.card V : ℚ) * scoring_norm_one s)
