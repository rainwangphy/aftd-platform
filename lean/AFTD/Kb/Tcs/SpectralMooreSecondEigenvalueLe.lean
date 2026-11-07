import AFTD.Prelude

/-!
# spectral_moore_second_eigenvalue_le

Topic: graphs   Node: 44126d87cafc

Provenance: formalization of a published result. Source: arXiv:2611.00591

For a finite simple graph G, the second largest adjacency eigenvalue is at most θ.
-/

open Classical SimpleGraph Matrix in
/-- The second largest eigenvalue of a finite simple graph G is at most θ. -/
noncomputable def spectral_moore_second_eigenvalue_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (θ : ℝ) : Prop := ∀ (i : Fin (Fintype.card V)), 0 < i.val → (G.isHermitian_adjMatrix ℝ).eigenvalues₀ i ≤ θ
