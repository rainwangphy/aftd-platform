import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsMaxWeight
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamTail

/-!
# fair_max_weight_lineup_majority_probability_three

Topic: algorithms   Node: 51ed36789612

Provenance: formalization of a published result. Source: arXiv:2605.21234, Team Order

For n = 3 players, every 3 × 3 matrix P of probabilities in [0, 1] with an all-fair maximum-weight matching M satisfies team_winProb P σ ≤ 9/16 for every lineup permutation σ.
-/

lemma fair_max_weight_lineup_majority_probability_three_ofFn {α : Type*} (f : Fin 3 → α) :
    List.ofFn f = [f 0, f 1, f 2] := by
  simp [List.ofFn_succ]

lemma fair_max_weight_lineup_majority_probability_three_aux (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h_sum : a + b + c ≤ 3 / 2) (hc_half : c ≤ 1 / 2) :
    a * b + a * c + b * c - 2 * a * b * c ≤ 9 / 16 := by
  have h_id : 9 / 16 - (a * b + a * c + b * c - 2 * a * b * c) =
      c * (4 * c ^ 2 + 3 * (1 - 2 * c)) / 8 +
      (3 / 2 - c - (a + b)) * ((3 / 2 - c + (a + b)) / 4 * (1 - 2 * c) + c) +
      ((a - b) ^ 2 / 4) * (1 - 2 * c) := by ring
  have h_c1 : 0 ≤ 1 - 2 * c := by linarith
  have h_t1 : 0 ≤ c * (4 * c ^ 2 + 3 * (1 - 2 * c)) / 8 := by
    have : 0 ≤ 4 * c ^ 2 + 3 * (1 - 2 * c) := by positivity
    positivity
  have h_t2 : 0 ≤ (3 / 2 - c - (a + b)) * ((3 / 2 - c + (a + b)) / 4 * (1 - 2 * c) + c) := by
    have h1 : 0 ≤ 3 / 2 - c - (a + b) := by linarith
    have h2 : 0 ≤ (3 / 2 - c + (a + b)) / 4 * (1 - 2 * c) + c := by
      have : 0 ≤ 3 / 2 - c + (a + b) := by linarith
      positivity
    exact mul_nonneg h1 h2
  have h_t3 : 0 ≤ ((a - b) ^ 2 / 4) * (1 - 2 * c) := by positivity
  linarith

lemma fair_max_weight_lineup_majority_probability_three_symm (q0 q1 q2 : ℝ)
    (h0 : 0 ≤ q0) (h1 : 0 ≤ q1) (h2 : 0 ≤ q2)
    (hsum : q0 + q1 + q2 ≤ 3 / 2) :
    q0 * q1 + q0 * q2 + q1 * q2 - 2 * q0 * q1 * q2 ≤ 9 / 16 := by
  by_cases hc : q2 ≤ 1 / 2
  · exact fair_max_weight_lineup_majority_probability_three_aux q0 q1 q2 h0 h1 h2 hsum hc
  · by_cases hb : q1 ≤ 1 / 2
    · have h_symm : q0 * q1 + q0 * q2 + q1 * q2 - 2 * q0 * q1 * q2 =
          q0 * q2 + q0 * q1 + q2 * q1 - 2 * q0 * q2 * q1 := by ring
      rw [h_symm]
      have hsum' : q0 + q2 + q1 ≤ 3 / 2 := by linarith
      exact fair_max_weight_lineup_majority_probability_three_aux q0 q2 q1 h0 h2 h1 hsum' hb
    · by_cases ha : q0 ≤ 1 / 2
      · have h_symm : q0 * q1 + q0 * q2 + q1 * q2 - 2 * q0 * q1 * q2 =
            q1 * q2 + q1 * q0 + q2 * q0 - 2 * q1 * q2 * q0 := by ring
        rw [h_symm]
        have hsum' : q1 + q2 + q0 ≤ 3 / 2 := by linarith
        exact fair_max_weight_lineup_majority_probability_three_aux q1 q2 q0 h1 h2 h0 hsum' ha
      · linarith

/-- The 9/16 lineup upper bound holds for the smallest open instance size n = 3. -/
theorem fair_max_weight_lineup_majority_probability_three
    (P : Fin 3 → Fin 3 → ℝ) (hP : ∀ i j, 0 ≤ P i j ∧ P i j ≤ 1)
    (M : Equiv.Perm (Fin 3)) (hM_max : team_isMaxWeight P M)
    (hM_half : ∀ i, P i (M i) = 1 / 2)
    (σ : Equiv.Perm (Fin 3)) :
    team_winProb P σ ≤ 9 / 16 := by
  have h1 : team_weight P σ ≤ team_weight P M := hM_max σ
  unfold team_weight at h1
  have h2 : (∑ i : Fin 3, P i (M i)) = 3 / 2 := by
    rw [Fin.sum_univ_three]
    rw [hM_half 0, hM_half 1, hM_half 2]
    norm_num
  have h_sum : P 0 (σ 0) + P 1 (σ 1) + P 2 (σ 2) ≤ 3 / 2 := by
    rw [Fin.sum_univ_three] at h1
    linarith
  have h_tail : team_winProb P σ =
      P 0 (σ 0) * P 1 (σ 1) + P 0 (σ 0) * P 2 (σ 2) + P 1 (σ 1) * P 2 (σ 2) -
      2 * P 0 (σ 0) * P 1 (σ 1) * P 2 (σ 2) := by
    unfold team_winProb
    change team_tail (List.ofFn fun i => P i (σ i)) 2 = _
    rw [fair_max_weight_lineup_majority_probability_three_ofFn]
    dsimp [team_tail]
    ring
  rw [h_tail]
  exact fair_max_weight_lineup_majority_probability_three_symm
    (P 0 (σ 0)) (P 1 (σ 1)) (P 2 (σ 2))
    (hP 0 (σ 0)).1 (hP 1 (σ 1)).1 (hP 2 (σ 2)).1 h_sum
