import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CandidateRank
import AFTD.Kb.GameTheoryEconomics.RankScoreCandidateWeight
import AFTD.Kb.GameTheoryEconomics.IsPositionalScoringVector
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.ScoringLast

/-!
# rank_score_candidate_weight_pos_of_last_pos

Topic: social_choice   Node: 6eafa42d1c47

Provenance: helper lemma. step towards rank_score_veto_core_tightness_conjecture

If s is a positional scoring vector whose last-place score is positive then every candidate has strictly positive rank-score weight.
-/

/-- Positive last-place score makes every candidate's rank-score weight positive, so the fractional matching puts mass on every candidate. -/
theorem rank_score_candidate_weight_pos_of_last_pos :
    ∀ (C : Type*) [Fintype C] [DecidableEq C] (hm : 2 ≤ Fintype.card C)
      (s : Fin (Fintype.card C) → ℚ) (hs : is_positional_scoring_vector (Fintype.card C) s)
      (hs_last : 0 < scoring_last (Fintype.card C) (by omega) s)
      (V : Type*) [Fintype V] [Nonempty V]
      (prof : V → LinearOrder C) (c : C),
      0 < rank_score_candidate_weight s prof c := by
  intro C _ _ hm s hs hs_last V _ _ prof c
  have h_elem_pos : ∀ k : Fin (Fintype.card C), 0 < s k := by
    intro k
    have h_le : k ≤ ⟨Fintype.card C - 1, by omega⟩ := by
      rw [Fin.le_def]
      exact Nat.le_pred_of_lt k.isLt
    have h_s := hs.1 k ⟨Fintype.card C - 1, by omega⟩ h_le
    dsimp [scoring_last] at hs_last
    exact lt_of_lt_of_le hs_last h_s
  have h_num_pos : 0 < ∑ v : V, s (candidate_rank (prof v) c) := by
    apply Finset.sum_pos
    · intro v _
      exact h_elem_pos (candidate_rank (prof v) c)
    · exact Finset.univ_nonempty
  have h_V_pos : (0 : ℚ) < (Fintype.card V : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  have h_norm_pos : 0 < scoring_norm_one s := by
    dsimp [scoring_norm_one]
    apply Finset.sum_pos
    · intro i _
      exact h_elem_pos i
    · have : 0 < Fintype.card C := by omega
      exact ⟨⟨0, this⟩, Finset.mem_univ _⟩
  have h_den_pos : 0 < (Fintype.card V : ℚ) * scoring_norm_one s := mul_pos h_V_pos h_norm_pos
  dsimp [rank_score_candidate_weight]
  exact div_pos h_num_pos h_den_pos
