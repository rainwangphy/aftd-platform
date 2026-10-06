import AFTD.Prelude
import AFTD.Kb.Tcs.TeamWeight
import AFTD.Kb.Tcs.TeamWinProb
import AFTD.Kb.Tcs.TeamIsOptimal
import AFTD.Kb.Tcs.TeamP2
import AFTD.Kb.Tcs.TeamP2Bounds
import AFTD.Kb.Tcs.TeamWeight2Id
import AFTD.Kb.Tcs.Team2UniqueMaxWeight
import AFTD.Kb.Tcs.TeamIdWinProb2
import AFTD.Kb.Tcs.TeamRotWinProb2
import AFTD.Kb.Tcs.TeamThm4Part2Exists

/-!
# team_thm4_part2_exists_false

Topic: algorithms   Node: 773fa800b7ff

Provenance: erratum. Corrects: The Team Order Problem: Maximizing the Probability of Matching Being Large Enough, SAGT 2024 (arXiv:2605.21234), Section 6, Theorem 4(2), even in its existential reading (some maximum-weight matching satisfies the bound): false for every o(1) function; unique all-1/2 maximum-weight matching, gap at least 1/40

Even the existential reading of Theorem 4 (2) of arXiv:2605.21234 is false, for every function ε in place of o(1): on the (2m+3)-player strengthened instance the all-1/2 identity is the unique maximum-weight matching (so the error term is 0), it wins with probability 1/2, and the optimal line-up wins with probability at least 1/2 + 1/40.
-/

open Finset in
/-- Even the existential reading of Theorem 4 (2) of arXiv:2605.21234 is false, for every function `ε` in place of `o(1)`: on the `(2m+3)`-player strengthened instance the all-`1/2` identity is the unique maximum-weight matching (so the error term is `0`), it wins with probability `1/2`, and the optimal line-up wins with probability at least `1/2 + 1/40`. -/
theorem team_thm4_part2_exists_false (ε : ℕ → ℝ) (N : ℕ) : ¬ team_thm4_part2_exists ε N := by
  intro h
  obtain ⟨O, -, hO⟩ := Finset.exists_max_image (univ : Finset (Equiv.Perm (Fin (2 * N + 3))))
    (team_winProb (team_P2 N)) ⟨1, Finset.mem_univ _⟩
  have hOpt : team_isOptimal (team_P2 N) O := fun σ => hO σ (Finset.mem_univ _)
  obtain ⟨M, hM, hbound⟩ := h (2 * N + 3) (by omega) (team_P2 N) (team_P2_bounds N) O hOpt
  have hM1 : M = 1 := (team2_unique_maxWeight N M).1 hM
  subst hM1
  have hn : (((2 * N + 3 : ℕ) : ℝ)) / 2 = team_weight (team_P2 N) 1 := (team_weight2_id N).symm
  have hsl : 0 ≤ Real.sqrt ((2 * N + 3 : ℕ) : ℝ) * Real.log ((2 * N + 3 : ℕ) : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_cast; omega))
  have key := hbound (by linarith) (by linarith)
  have hsq : ∑ i : Fin (2 * N + 3), (team_P2 N i ((1 : Equiv.Perm (Fin (2 * N + 3))) i) - 1 / 2) ^ 2
      = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [team_P2]
  rw [hsq, mul_zero, add_zero, team_id_winProb2] at key
  have hrot := hOpt (finRotate (2 * N + 3))
  have := team_rot_winProb2 N
  linarith
