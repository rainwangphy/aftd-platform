import AFTD.Prelude

/-!
# is_fractional_clique_cover

Topic: graphs   Node: 84347562fb75

Provenance: formalization of a published result. Source: arXiv:2610.41371 Def. 2.2

A fractional K_r-cover of a graph G is an edge weighting w : Sym2 V → ℚ taking values in [0, 1] on edges of G such that for every r-clique Q in G, the sum of weights of edges in Q is at least 1.
-/

/-- Definition of a fractional K_r-cover of a graph G. -/
def is_fractional_clique_cover {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℚ) (r : ℕ) : Prop :=
  (∀ e ∈ G.edgeSet, 0 ≤ w e ∧ w e ≤ 1) ∧
  ∀ (Q : Finset V), G.IsNClique r Q →
    1 ≤ ∑ e ∈ Q.offDiag.image (fun p => s(p.1, p.2)), w e
