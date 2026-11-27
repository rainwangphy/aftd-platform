import AFTD.Prelude

/-!
# op874_unselected_edge_two_bad_nonowners_impossible

Topic: graphs   Node: d707b9533bd4

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

Two adjacent nonowner vertices cannot have the displayed four-high-color palettes and disjoint exposed hidden colors at an unselected edge using the common pair.
-/

theorem op874_unselected_edge_two_bad_nonowners_impossible
    (t s₁ s₂ x₁ x₂ y₁ y₂ : Fin 6)
    (htlo : 2 ≤ t.val) (hthi : t.val ≤ 3)
    (hs₁ : 4 ≤ s₁.val) (hs₂ : 4 ≤ s₂.val)
    (hx₁ : 4 ≤ x₁.val) (hx₂ : 4 ≤ x₂.val)
    (hy₁ : 2 ≤ y₁.val) (hy₂ : 2 ≤ y₂.val)
    (hsx₁ : s₁ ≠ x₁) (hsx₂ : s₂ ≠ x₂)
    (hys₁ : y₁ ≠ s₁) (hys₂ : y₂ ≠ s₂)
    (hyx₁ : y₁ ≠ x₁) (hyx₂ : y₂ ≠ x₂)
    (hyt₁ : y₁ ≠ t) (hyt₂ : y₂ ≠ t) (hyy : y₁ ≠ y₂) : False := by
  have hsx₁' : s₁.val ≠ x₁.val := fun h => hsx₁ (Fin.ext h)
  have hsx₂' : s₂.val ≠ x₂.val := fun h => hsx₂ (Fin.ext h)
  have hys₁' : y₁.val ≠ s₁.val := fun h => hys₁ (Fin.ext h)
  have hys₂' : y₂.val ≠ s₂.val := fun h => hys₂ (Fin.ext h)
  have hyx₁' : y₁.val ≠ x₁.val := fun h => hyx₁ (Fin.ext h)
  have hyx₂' : y₂.val ≠ x₂.val := fun h => hyx₂ (Fin.ext h)
  have hyt₁' : y₁.val ≠ t.val := fun h => hyt₁ (Fin.ext h)
  have hyt₂' : y₂.val ≠ t.val := fun h => hyt₂ (Fin.ext h)
  have hyy' : y₁.val ≠ y₂.val := fun h => hyy (Fin.ext h)
  have b₁ := s₁.isLt
  have b₂ := s₂.isLt
  have b₃ := x₁.isLt
  have b₄ := x₂.isLt
  have b₅ := y₁.isLt
  have b₆ := y₂.isLt
  have y₁small : y₁.val ≤ 3 := by omega
  have y₂small : y₂.val ≤ 3 := by omega
  omega
