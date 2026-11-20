import AFTD.Prelude

/-!
# CorrespondenceCover

Topic: graphs   Node: c3680cf1bed3

Provenance: formalization of a published result. Source: arXiv:2611.24832, Section 1

An m-fold correspondence cover of a simple graph F is a graph H on V × Fin m such that each fiber {v} × Fin m is a clique in H, edges between fibers of distinct non-adjacent vertices of F are absent in H, and for every edge uv of F the edges of H between {u} × Fin m and {v} × Fin m form a matching.
-/

/-- An m-fold correspondence cover (DP-cover) of a simple graph F on fibers V × Fin m. -/
structure CorrespondenceCover {V : Type*} (F : SimpleGraph V) (m : ℕ) where
  H : SimpleGraph (V × Fin m)
  clique : ∀ v (i j : Fin m), i ≠ j → H.Adj (v, i) (v, j)
  nonadj : ∀ {u v : V} (i j : Fin m), ¬ F.Adj u v → u ≠ v → ¬ H.Adj (u, i) (v, j)
  matching : ∀ {u v : V}, F.Adj u v → ∀ (i : Fin m) (j₁ j₂ : Fin m),
    H.Adj (u, i) (v, j₁) → H.Adj (u, i) (v, j₂) → j₁ = j₂
