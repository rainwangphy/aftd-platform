import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphResidualAt
import AFTD.Kb.Tcs.DigraphClosedOutNbr

/-!
# digraph_residual_subset_out_nbr

Topic: graphs   Node: 35d202ef603c

Provenance: helper lemma. arXiv:2611.32872 p. 3

For a finite type V with decidable equality, directed graphs G and H of type Digraph V with decidable adjacency relations, and any vertex v : V, the residual set digraph_residual_at G H v is a subset of the closed out-neighborhood digraph_closed_out_nbr H {v}.
-/

/-- The residual R_v at vertex v is contained in the closed out-neighborhood N_H⁺[v]. -/
theorem digraph_residual_subset_out_nbr {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (v : V) :
    digraph_residual_at G H v ⊆ digraph_closed_out_nbr H {v} := by
  intro w hw
  simp only [digraph_residual_at, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  have h := hw v (Or.inl rfl)
  simp only [digraph_closed_out_nbr, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rcases h with rfl | vadj
  · left; rfl
  · right
    exact ⟨v, rfl, vadj⟩
