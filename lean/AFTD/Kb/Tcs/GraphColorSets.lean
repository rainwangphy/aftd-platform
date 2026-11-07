import AFTD.Prelude

/-!
# graph_color_sets

Topic: graphs   Node: 36155192f2f2

Provenance: formalization of a published result. Source: arXiv:2611.07924, Section 1

Given a finite vertex type V, a simple graph G on V, and a list assignment L : V → Finset ℕ assigning each vertex a finite set of colors in ℕ, graph_color_sets G L is the Finset of Finset ℕ consisting of all image sets Finset.image φ Finset.univ of proper L-colorings φ : V → ℕ of G satisfying φ(v) ∈ L(v) for all v and φ(u) ≠ φ(v) for all adjacent u, v.
-/

/-- The Finset of all color sets φ(V) of proper L-colorings φ of a graph G with lists in ℕ. -/
noncomputable def graph_color_sets {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Fintype.piFinset L).filter (fun φ => ∀ u v, G.Adj u v → φ u ≠ φ v) |>.image (fun φ => Finset.image φ Finset.univ)
