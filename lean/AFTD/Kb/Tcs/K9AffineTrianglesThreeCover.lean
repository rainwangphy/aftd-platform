import AFTD.Prelude
import AFTD.Kb.Tcs.K9AffineTriangle
import AFTD.Kb.Tcs.K9AffineTrianglesDiffColorInterCard

/-!
# k9_affine_triangles_three_cover

Topic: graphs   Node: b504a37f97cd

Provenance: formalization of a published result. Source: arXiv:2611.06362 Lemma 2.1

If three monochromatic triangles `k9_affine_triangle c₁ j₁`, `k9_affine_triangle c₂ j₂`, and `k9_affine_triangle c₃ j₃` cover all nine vertices of `(ZMod 3) × (ZMod 3)`, then they share the same colour `c₁ = c₂ ∧ c₂ = c₃` and their lines `j₁, j₂, j₃` are pairwise distinct.
-/

/-- Three monochromatic triangles cover all nine vertices of K9 only if they are the three triangles of one colour. -/
theorem k9_affine_triangles_three_cover (c₁ c₂ c₃ : Fin 4) (j₁ j₂ j₃ : ZMod 3)
    (hcov : k9_affine_triangle c₁ j₁ ∪ k9_affine_triangle c₂ j₂ ∪ k9_affine_triangle c₃ j₃ = Finset.univ) :
    c₁ = c₂ ∧ c₂ = c₃ ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ := by
  revert c₁ c₂ c₃ j₁ j₂ j₃
  decide
