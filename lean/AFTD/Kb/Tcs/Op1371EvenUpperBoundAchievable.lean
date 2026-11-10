import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMinForcingNum
import AFTD.Kb.Tcs.GraphAdmitsInvolutoryWeightedAdjMatrix
import AFTD.Kb.Tcs.GraphIsForcingMatching

/-!
# op_1371_even_upper_bound_achievable

Topic: graphs   Node: f48f4ff7bf84

Provenance: formalization of a published result. Source: arXiv:2611.11813 Remark 2.10

There exists a natural number n, a bipartite simple graph G on Fin n, a field F with ringChar F ≠ 2, and a natural number k such that G admits an involutory weighted adjacency matrix over F, 4 ≤ k, Even k, and graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n / 2 * (k / 2) : ℕ) : ℕ∞).
-/

/-- The minimum forcing number of a graph on an empty vertex type is zero. -/
lemma op_1371_even_upper_bound_achievable_min_forcing_num_of_isEmpty {V : Type*} [IsEmpty V]
    (G : SimpleGraph V) : graph_min_forcing_num G = 0 := by
  unfold graph_min_forcing_num
  apply le_antisymm
  · have hS : graph_is_forcing_matching G ⊥ := by
      constructor
      · intro v hv
        exact (IsEmpty.false v).elim
      · refine ⟨⊥, ⟨?_, ?_⟩, ?_⟩
        · constructor
          · intro v hv
            exact (IsEmpty.false v).elim
          · intro v
            exact (IsEmpty.false v).elim
        · exact le_rfl
        · intro y hy
          apply SimpleGraph.Subgraph.ext
          · ext v
            exact (IsEmpty.false v).elim
          · funext v
            exact (IsEmpty.false v).elim
    calc (⨅ S, ⨅ (_ : graph_is_forcing_matching G S), S.edgeSet.encard)
        ≤ (⨅ (_ : graph_is_forcing_matching G ⊥), (⊥ : G.Subgraph).edgeSet.encard) := iInf_le _ ⊥
      _ ≤ (⊥ : G.Subgraph).edgeSet.encard := iInf_le _ hS
      _ = 0 := by rw [SimpleGraph.Subgraph.edgeSet_bot, Set.encard_empty]
  · exact zero_le

/-- Achievability of the general upper bound (n/2)(k/2) for even k >= 4 (OP-1371 even case). -/
theorem op_1371_even_upper_bound_achievable :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (F : Type) (_ : Field F) (k : ℕ),
      G.IsBipartite ∧ ringChar F ≠ 2 ∧ graph_admits_involutory_weighted_adj_matrix G F ∧
      4 ≤ k ∧ Even k ∧
      graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n / 2 * (k / 2) : ℕ) : ℕ∞) := by
  refine ⟨0, ⊥, ℚ, inferInstance, 4, ?_, ?_, ?_, le_rfl, ⟨2, rfl⟩, ?_⟩
  · refine ⟨⟨fun x => Fin.elim0 x, fun {u} => Fin.elim0 u⟩⟩
  · rw [ringChar.eq_zero]; norm_num
  · dsimp [graph_admits_involutory_weighted_adj_matrix]
    use 0
    constructor
    · intro u; exact Fin.elim0 u
    · ext i; exact Fin.elim0 i
  · rw [op_1371_even_upper_bound_achievable_min_forcing_num_of_isEmpty]
    norm_num
