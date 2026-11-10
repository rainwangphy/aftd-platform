import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMinForcingNum
import AFTD.Kb.Tcs.GraphAdmitsInvolutoryWeightedAdjMatrix
import AFTD.Kb.Tcs.Op1371MinForcingNumUpperBoundAchievable

/-!
# op_1371_odd_improved_upper_bound_achievable

Topic: graphs   Node: cd69c7e4a70a

Provenance: formalization of a published result. Source: arXiv:2611.11813 Remark 2.10

There exists a natural number n, a bipartite simple graph G on Fin n, a field F with ringChar F ≠ 2, and a natural number k such that G admits an involutory weighted adjacency matrix over F, 3 ≤ k, Odd k, and graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n * (k - 1) / 4 : ℕ) : ℕ∞) + graph_min_forcing_num G.
-/

/-- Achievability of the improved upper bound n(k-1)/4 + f(G) for odd k >= 3 (OP-1371 odd case). -/
theorem op_1371_odd_improved_upper_bound_achievable :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (F : Type) (_ : Field F) (k : ℕ),
      G.IsBipartite ∧ ringChar F ≠ 2 ∧ graph_admits_involutory_weighted_adj_matrix G F ∧
      3 ≤ k ∧ Odd k ∧
      graph_min_forcing_num (G □ SimpleGraph.pathGraph k) =
        ((n * (k - 1) / 4 : ℕ) : ℕ∞) + graph_min_forcing_num G := by
  refine ⟨0, ⊥, ℚ, inferInstance, 3, ?_, ?_, ?_, le_rfl, ⟨1, rfl⟩, ?_⟩
  · refine ⟨⟨fun x => Fin.elim0 x, fun {u} => Fin.elim0 u⟩⟩
  · simp
  · dsimp [graph_admits_involutory_weighted_adj_matrix]
    use 0
    constructor
    · intro u; exact Fin.elim0 u
    · ext i; exact Fin.elim0 i
  · rw [op_1371_min_forcing_num_upper_bound_achievable_min_forcing_num_of_isEmpty]
    rw [op_1371_min_forcing_num_upper_bound_achievable_min_forcing_num_of_isEmpty]
    rfl
