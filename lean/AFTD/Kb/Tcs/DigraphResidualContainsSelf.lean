import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphResidualAt

/-!
# digraph_residual_contains_self

Topic: graphs   Node: 0e97b08344ad

Provenance: helper lemma. arXiv:2611.32872 p. 3

For a finite type V with decidable equality, directed graphs G and H of type Digraph V with decidable adjacency relations, if G ≤ H, then every vertex v : V satisfies v ∈ digraph_residual_at G H v.
-/

/-- Every vertex v belongs to its own residual R_v. -/
theorem digraph_residual_contains_self {V : Type*} [Fintype V] [DecidableEq V]
    (G H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (v : V) :
    v ∈ digraph_residual_at G H v := by
  simp only [digraph_residual_at, Finset.mem_filter, Finset.mem_univ, true_and]
  intro u hu
  rcases hu with rfl | hadj
  · left; rfl
  · right; exact hGH hadj
