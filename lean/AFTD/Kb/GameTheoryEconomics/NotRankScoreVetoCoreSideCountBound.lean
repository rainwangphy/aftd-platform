import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankScoreVetoCoreHallSubsetCount
import AFTD.Kb.GameTheoryEconomics.IsPositionalScoringVector
import AFTD.Kb.GameTheoryEconomics.ScoringLast
import AFTD.Kb.GameTheoryEconomics.CandidateRank
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.IsRankScoreVetoCore
import AFTD.Kb.GameTheoryEconomics.RankScoreCandidateWeight

/-!
# not_rank_score_veto_core_side_count_bound

Topic: social_choice   Node: 9cca153c326c

Provenance: original. Related work: refutes `rank_score_veto_core_side_count_bound`

The statement `rank_score_veto_core_side_count_bound` is false: The conclusion has its two cardinalities swapped with respect to the paper's lemma (and with respect to the informal statement). In Lean, `candidate_rank ord c = #{c' : c < c'}` (verified: rank of the top element of `Fin 3` is 0, of the bottom is 2), so `(prof v).lt x y` means voter v ranks y strictly ABOVE x, i.e. `x <_v y` iff voter v PREFERS y to x. Thus the Lean left-hand side `#{v : c_star <_v a}` counts voters preferring **a**, whereas the informal statement defines G = `#{v : c* <_v a}` as the voters preferring **c***. The paper's lemma (encoded by the proved `rank_score_veto_core_hall_condition` as `n₂ ≤ n₁·Δ` with n₁ = voters preferring a) is `#{v : prefers c*} ≤ Δ · #{v : prefers a}`, i.e. in Lean `#{v : a <_v c_star} ≤ Δ · #{v : c_star <_v a}`. The statement as written asserts the reverse.

Concrete refutation: take C = ULift (Fin 3) with the standard order, V = ULift (Fin 1) (one voter), s ≡ 1 (a legal positional scoring vector: nonincreasing, nonnegative, s(0) = 1, so ||s||₁ = 3, s_last = 1 > 0), a = ULift.up 2 (the top candidate) and c_star = ULift.up 1. Since a is top, every candidate satisfies c ≤_v a, so the fractional matching w(v,c) = 1/3 has all its mass on candidates weakly below a; all four clauses of `is_rank_score_veto_core` hold (row sums 1 = 1/|V|, column sums 1/3 = rank-score weight of every candidate). But the conclusion becomes `#{v : 1 < 2} ≤ (3 - 1) * #{v : 2 < 1}`, i.e. `1 ≤ 2 * 0 = 0`, which is false. The hypothesis `3 ≤ Fintype.card C` is satisfied (exactly 3 candidates), so it does not save the statement (the m = 2 analogue fails the same way).

Suggested fix: swap the two filters in the conclusion.
-/

theorem not_rank_score_veto_core_side_count_bound : ¬ (∀ (C : Type*) [Fintype C] [DecidableEq C] (hm : 3 ≤ Fintype.card C)
      (s : Fin (Fintype.card C) → ℚ) (hs : is_positional_scoring_vector (Fintype.card C) s)
      (hs_last : 0 < scoring_last (Fintype.card C) (by omega) s)
      (V : Type*) [Fintype V] [Nonempty V]
      (prof : V → LinearOrder C)
      (a : C) (ha : is_rank_score_veto_core s prof a)
      (c_star : C),
      ((Finset.univ.filter (fun v : V => (prof v).lt c_star a)).card : ℝ) ≤
        (((scoring_norm_one s - scoring_last (Fintype.card C) (by omega) s) : ℚ) : ℝ) *
          ((Finset.univ.filter (fun v : V => (prof v).lt a c_star)).card : ℝ)) := by
  intro h
  have hs : is_positional_scoring_vector (Fintype.card (ULift.{_,0} (Fin 3))) (fun _ => (1:ℚ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij; simp
    · intro i; norm_num
    · exact ⟨by simp, by simp⟩
  have ha : is_rank_score_veto_core (C := ULift.{_,0} (Fin 3)) (V := ULift.{_,0} (Fin 1))
      (fun _ => (1:ℚ)) (fun _ => (inferInstance : LinearOrder (ULift (Fin 3)))) (ULift.up 2) := by
    refine ⟨fun _ _ => 1/3, ?_, ?_, ?_, ?_⟩
    · intro v c; norm_num
    · intro v c _; change c.down ≤ (2 : Fin 3); exact Fin.le_last c.down
    · intro v; simp
    · intro c; simp [rank_score_candidate_weight, scoring_norm_one]
  have hmain := h (ULift.{_,0} (Fin 3)) (by simp) (fun _ => (1:ℚ)) hs
    (by simp [scoring_last]) (ULift.{_,0} (Fin 1))
    (fun _ => (inferInstance : LinearOrder (ULift (Fin 3)))) (ULift.up 2) ha (ULift.up 1)
  simp [scoring_last] at hmain
  norm_num at hmain
