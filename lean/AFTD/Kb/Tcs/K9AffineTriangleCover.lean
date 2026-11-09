import AFTD.Prelude
import AFTD.Kb.Tcs.K9AffineTriangle
import AFTD.Kb.Tcs.K9AffineTrianglesDiffColorInterCard
import AFTD.Kb.Tcs.K9AffineTrianglesThreeCover

/-!
# k9_affine_triangle_cover

Topic: graphs   Node: ab092636e625

Provenance: formalization of a published result. Source: arXiv:2611.06362 Lemma 2.1

In the affine-plane four-colouring of K9: (1) any three monochromatic triangles `k9_affine_triangle` covering all nine vertices must share the same colour and have pairwise distinct lines; and (2) any four monochromatic triangles `k9_affine_triangle c₁ j₁`, `k9_affine_triangle c₂ j₂`, `k9_affine_triangle c₃ j₃`, `k9_affine_triangle c₄ j₄` covering all nine vertices either contain all three triangles of some colour `c : Fin 4`, or have four pairwise distinct colours and share a common vertex `v : ZMod 3 × ZMod 3` (repetitions allowed).
-/

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 20000000 in
private theorem k9_affine_triangle_cover_four :
    ∀ (c₁ c₂ c₃ c₄ : Fin 4) (j₁ j₂ j₃ j₄ : ZMod 3),
      k9_affine_triangle c₁ j₁ ∪ k9_affine_triangle c₂ j₂ ∪
      k9_affine_triangle c₃ j₃ ∪ k9_affine_triangle c₄ j₄ = Finset.univ →
        (∃ c : Fin 4, ∀ j : ZMod 3,
          (c, j) = (c₁, j₁) ∨ (c, j) = (c₂, j₂) ∨ (c, j) = (c₃, j₃) ∨ (c, j) = (c₄, j₄)) ∨
        ((c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₁ ≠ c₄ ∧ c₂ ≠ c₃ ∧ c₂ ≠ c₄ ∧ c₃ ≠ c₄) ∧
          ∃ v : ZMod 3 × ZMod 3,
            v ∈ k9_affine_triangle c₁ j₁ ∧ v ∈ k9_affine_triangle c₂ j₂ ∧
            v ∈ k9_affine_triangle c₃ j₃ ∧ v ∈ k9_affine_triangle c₄ j₄) := by
  decide

/-- Monochromatic triangle coverings in the affine-plane four-colouring of K9 (Lemma 2.1). -/
theorem k9_affine_triangle_cover :
    (∀ (c₁ c₂ c₃ : Fin 4) (j₁ j₂ j₃ : ZMod 3),
      k9_affine_triangle c₁ j₁ ∪ k9_affine_triangle c₂ j₂ ∪ k9_affine_triangle c₃ j₃ = Finset.univ →
        c₁ = c₂ ∧ c₂ = c₃ ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    (∀ (c₁ c₂ c₃ c₄ : Fin 4) (j₁ j₂ j₃ j₄ : ZMod 3),
      k9_affine_triangle c₁ j₁ ∪ k9_affine_triangle c₂ j₂ ∪
      k9_affine_triangle c₃ j₃ ∪ k9_affine_triangle c₄ j₄ = Finset.univ →
        (∃ c : Fin 4, ∀ j : ZMod 3,
          (c, j) = (c₁, j₁) ∨ (c, j) = (c₂, j₂) ∨ (c, j) = (c₃, j₃) ∨ (c, j) = (c₄, j₄)) ∨
        ((c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₁ ≠ c₄ ∧ c₂ ≠ c₃ ∧ c₂ ≠ c₄ ∧ c₃ ≠ c₄) ∧
          ∃ v : ZMod 3 × ZMod 3,
            v ∈ k9_affine_triangle c₁ j₁ ∧ v ∈ k9_affine_triangle c₂ j₂ ∧
            v ∈ k9_affine_triangle c₃ j₃ ∧ v ∈ k9_affine_triangle c₄ j₄)) := ⟨k9_affine_triangles_three_cover, k9_affine_triangle_cover_four⟩
