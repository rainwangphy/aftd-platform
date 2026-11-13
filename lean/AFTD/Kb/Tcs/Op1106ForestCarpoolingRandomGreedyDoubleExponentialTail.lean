import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.ForestCarpoolMaximumFibonacciTail
import AFTD.Kb.Tcs.ForestCarpoolEnvelopeExp
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope

/-!
# op_1106_forest_carpooling_random_greedy_double_exponential_tail

Topic: online_algorithms   Node: e8816048fa01

Provenance: original. Related work: OP-1106, proposed in this research system; related work arXiv:2611.00388 studies a different algorithm on general fixed sequences and does not pose this forest question.

There exist absolute positive real constants c, C, and a such that for every natural number n, every forest edge sequence of length T ≥ 2 on Fin n, and every integer D ≥ 1, the uniform probability over all 2^T fair coin assignments that randomized greedy carpooling achieves maximum prefix discrepancy at least D is at most C * T * exp(-c * 2^(a * D)).
-/

/-- Conjecture OP-1106: Randomized greedy carpooling achieves a doubly exponential tail bound on every oblivious forest edge arrival sequence. -/
theorem op_1106_forest_carpooling_random_greedy_double_exponential_tail :
    ∃ (c C a : ℝ), 0 < c ∧ 0 < C ∧ 0 < a ∧
      ∀ (n : ℕ) (edges : List (Fin n × Fin n))
        (hT : 2 ≤ edges.length)
        (hforest : CarpoolForestEdgeSequence n edges)
        (D : ℕ) (hD : 1 ≤ D),
        let T := edges.length
        let high_discrepancy := Finset.univ.filter (fun r : Fin T → Bool =>
          D ≤ carpool_max_discrepancy n edges
            (carpool_greedy_orientations n edges (List.ofFn r)))
        ((high_discrepancy.card : ℝ) / (2 ^ T : ℝ)) ≤
          C * (T : ℝ) * Real.exp (-c * (2 : ℝ) ^ (a * (D : ℝ))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 4, 4, 1 / 2, by positivity, by norm_num, by norm_num, ?_⟩
  intro n edges hT hforest D hD
  dsimp only
  have hm := forest_carpool_maximum_fibonacci_tail n edges hforest D hD
  have he := forest_carpool_envelope_exp D hD
  have hfactor : 0 ≤ 4 * (edges.length : ℝ) := by positivity
  have hb := mul_le_mul_of_nonneg_left he hfactor
  have hExp : (1 / 2 : ℝ) * (D : ℝ) = (D : ℝ) / 2 := by ring
  rw [hExp]
  exact le_trans hm hb
