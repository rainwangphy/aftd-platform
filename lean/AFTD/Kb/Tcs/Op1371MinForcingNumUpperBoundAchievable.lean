import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMinForcingNum
import AFTD.Kb.Tcs.GraphAdmitsInvolutoryWeightedAdjMatrix
import AFTD.Kb.Tcs.GraphIsForcingMatching

/-!
# op_1371_min_forcing_num_upper_bound_achievable

Topic: graphs   Node: c9795bf6eb0c

Provenance: formalization of a published result. Source: arXiv:2611.11813 Remark 2.10

There exists a natural number n, a bipartite simple graph G on Fin n, a field F with ringChar F ≠ 2, such that G admits an involutory weighted adjacency matrix over F, and there exists a natural number k such that either 4 ≤ k, Even k, and graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n / 2 * (k / 2) : ℕ) : ℕ∞), or 3 ≤ k, Odd k, and graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n * (k - 1) / 4 : ℕ) : ℕ∞) + graph_min_forcing_num G.
-/

lemma op_1371_min_forcing_num_upper_bound_achievable_min_forcing_num_of_isEmpty
    {V : Type*} [IsEmpty V] (G : SimpleGraph V) :
    graph_min_forcing_num G = 0 := by
  dsimp [graph_min_forcing_num]
  have hS : graph_is_forcing_matching G ⊥ := by
    dsimp [graph_is_forcing_matching, SimpleGraph.Subgraph.IsMatching, SimpleGraph.Subgraph.IsPerfectMatching, SimpleGraph.Subgraph.IsSpanning]
    refine ⟨fun v _ => False.elim (IsEmpty.false v), ?_⟩
    refine ⟨⊥, ⟨⟨fun v _ => False.elim (IsEmpty.false v), fun v => False.elim (IsEmpty.false v)⟩, le_rfl⟩, ?_⟩
    rintro M ⟨⟨_, _⟩, _⟩
    ext v
    · exact False.elim (IsEmpty.false v)
    · exact False.elim (IsEmpty.false v)
  have he : (⊥ : G.Subgraph).edgeSet.encard = 0 := by
    rw [show (⊥ : G.Subgraph).edgeSet = ∅ by
      ext e
      rcases e with ⟨u, v⟩
      exact False.elim (IsEmpty.false u)]
    exact Set.encard_empty
  apply le_antisymm
  · have hle : (⨅ S, ⨅ (_ : graph_is_forcing_matching G S), S.edgeSet.encard) ≤
        ⨅ (_ : graph_is_forcing_matching G ⊥), (⊥ : G.Subgraph).edgeSet.encard :=
      iInf_le _ ⊥
    have hle2 : (⨅ (_ : graph_is_forcing_matching G ⊥), (⊥ : G.Subgraph).edgeSet.encard) ≤
        (⊥ : G.Subgraph).edgeSet.encard :=
      iInf_le _ hS
    have hle3 := le_trans hle hle2
    rwa [he] at hle3
  · exact bot_le

/-- Achievability of upper bounds on minimum forcing numbers of products with paths (OP-1371). -/
theorem op_1371_min_forcing_num_upper_bound_achievable :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (F : Type) (_ : Field F),
      G.IsBipartite ∧ ringChar F ≠ 2 ∧ graph_admits_involutory_weighted_adj_matrix G F ∧
      ∃ k : ℕ,
        (4 ≤ k ∧ Even k ∧
          graph_min_forcing_num (G □ SimpleGraph.pathGraph k) = ((n / 2 * (k / 2) : ℕ) : ℕ∞)) ∨
        (3 ≤ k ∧ Odd k ∧
          graph_min_forcing_num (G □ SimpleGraph.pathGraph k) =
            ((n * (k - 1) / 4 : ℕ) : ℕ∞) + graph_min_forcing_num G) := by
  refine ⟨0, ⊥, ℚ, inferInstance, ?_, ?_, ?_, 4, Or.inl ⟨le_rfl, ⟨2, rfl⟩, ?_⟩⟩
  · refine ⟨⟨fun x => Fin.elim0 x, fun {u} => Fin.elim0 u⟩⟩
  · simp
  · dsimp [graph_admits_involutory_weighted_adj_matrix]
    use 0
    constructor
    · intro u; exact Fin.elim0 u
    · ext i; exact Fin.elim0 i
  · rw [op_1371_min_forcing_num_upper_bound_achievable_min_forcing_num_of_isEmpty]
    rfl
