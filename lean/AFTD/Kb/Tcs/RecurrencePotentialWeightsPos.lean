import AFTD.Prelude
import AFTD.Kb.Tcs.SatisfiesRecurrence21
import AFTD.Kb.Tcs.RecurrencePotentialWeights

/-!
# recurrence_potential_weights_pos

Topic: combinatorics   Node: 097b94c15425

Provenance: helper lemma. arXiv:2611.01561, Proof of Lemma 2.1

For any recurrence satisfying (2.1), the potential weights π_i are strictly positive for all i : Fin (N + 1).
-/

/-- The potential weights are strictly positive under condition (2.1). -/
theorem recurrence_potential_weights_pos (N : ℕ) (a b c : Fin (N + 1) → ℝ)
    (hrec : satisfies_recurrence_2_1 N a b c) (i : Fin (N + 1)) :
    0 < recurrence_potential_weights N a c i := by
  unfold recurrence_potential_weights
  apply Finset.prod_pos
  intro j _
  obtain ⟨-, -, -, -, -, ha, hc⟩ := hrec
  have hj : j.val < i.val := j.isLt
  have hi : i.val < N + 1 := i.isLt
  apply div_pos
  · exact ha _ (by show j.val < N; omega)
  · exact hc _ (by show 0 < j.val + 1; omega)
