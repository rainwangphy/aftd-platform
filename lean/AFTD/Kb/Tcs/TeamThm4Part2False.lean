import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsOptimal
import AFTD.Kb.Tcs.TeamThm4Part2
import AFTD.Kb.Tcs.TeamP
import AFTD.Kb.Tcs.TeamPBounds
import AFTD.Kb.Tcs.TeamWeightId
import AFTD.Kb.Tcs.TeamIdMaxWeight
import AFTD.Kb.Tcs.TeamIdWinProb
import AFTD.Kb.Tcs.TeamRotWinProb

/-!
# team_thm4_part2_false

Topic: algorithms   Node: a911059aecce

Provenance: erratum. Corrects: The Team Order Problem: Maximizing the Probability of Matching Being Large Enough, SAGT 2024 (arXiv:2605.21234), Section 6, Theorem 4(2) (near weight n/2 an optimal line-up beats a maximum-weight matching M* by at most (4 + o(1))/(n+1) * sum over M* of (p_e - 1/2)^2): false for every choice of the o(1) term; (2m+3)-player instance with an all-1/2 maximum-weight matching and a gap of 1/16

Theorem 4 (2) of arXiv:2605.21234 is false, whatever function is used for its o(1) term: for every m, on the (2m+3)-player instance the identity line-up is a maximum-weight matching with all edge probabilities 1/2 (so w(M*) = n/2 and the error term vanishes) and wins with probability 1/2, while the optimal line-up wins with probability at least 9/16.
-/

open Finset in
/-- Theorem 4 (2) of arXiv:2605.21234 is false, whatever function is used for its `o(1)` term: for every `m`, on the `(2m+3)`-player instance the identity line-up is a maximum-weight matching with all edge probabilities `1/2` (so `w(M*) = n/2` and the error term vanishes) and wins with probability `1/2`, while the optimal line-up wins with probability at least `9/16`. -/
theorem team_thm4_part2_false (ε : ℕ → ℝ) (N : ℕ) : ¬ team_thm4_part2 ε N := by
  intro h
  obtain ⟨O, -, hO⟩ := Finset.exists_max_image (univ : Finset (Equiv.Perm (Fin (2 * N + 3))))
    (team_winProb (team_P N)) ⟨1, Finset.mem_univ _⟩
  have hOpt : team_isOptimal (team_P N) O := fun σ => hO σ (Finset.mem_univ _)
  have hn : (((2 * N + 3 : ℕ) : ℝ)) / 2 = team_weight (team_P N) 1 := (team_weight_id N).symm
  have hsl : 0 ≤ Real.sqrt ((2 * N + 3 : ℕ) : ℝ) * Real.log ((2 * N + 3 : ℕ) : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_cast; omega))
  have key := h (2 * N + 3) (by omega) (team_P N) (team_P_bounds N) 1 O
    (team_id_maxWeight N) hOpt (by linarith) (by linarith)
  have hsq : ∑ i : Fin (2 * N + 3), (team_P N i ((1 : Equiv.Perm (Fin (2 * N + 3))) i) - 1 / 2) ^ 2
      = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [team_P]
  rw [hsq, mul_zero, add_zero, team_id_winProb] at key
  have hrot := hOpt (finRotate (2 * N + 3))
  rw [team_rot_winProb] at hrot
  linarith
