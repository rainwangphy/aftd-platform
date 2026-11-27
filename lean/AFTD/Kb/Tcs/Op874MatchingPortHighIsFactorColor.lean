import AFTD.Prelude

/-!
# op874_matching_port_high_is_factor_color

Topic: graphs   Node: 36c1bb253d2c

Provenance: helper lemma. Structural reduction for the exact-owner global-pair route to OP-874; experiment 43048 tests the hypotheses.

If four distinct colors are drawn from the four high colors and a fifth high color differs from the last two, it equals one of the first two.
-/

theorem op874_matching_port_high_is_factor_color
    (c₁ c₂ h₁ h₂ x : Fin 6)
    (hc₁ : 2 ≤ c₁.val) (hc₂ : 2 ≤ c₂.val)
    (hh₁ : 2 ≤ h₁.val) (hh₂ : 2 ≤ h₂.val)
    (hc : c₁ ≠ c₂) (hc₁h₁ : c₁ ≠ h₁) (hc₁h₂ : c₁ ≠ h₂)
    (hc₂h₁ : c₂ ≠ h₁) (hc₂h₂ : c₂ ≠ h₂) (hh : h₁ ≠ h₂)
    (hxh₁ : x ≠ h₁) (hxh₂ : x ≠ h₂) (hx : 2 ≤ x.val) :
    x = c₁ ∨ x = c₂ := by
  have b₁ := c₁.isLt
  have b₂ := c₂.isLt
  have b₃ := h₁.isLt
  have b₄ := h₂.isLt
  have b₅ := x.isLt
  have a₁ : c₁.val ≠ c₂.val := fun h => hc (Fin.ext h)
  have a₂ : c₁.val ≠ h₁.val := fun h => hc₁h₁ (Fin.ext h)
  have a₃ : c₁.val ≠ h₂.val := fun h => hc₁h₂ (Fin.ext h)
  have a₄ : c₂.val ≠ h₁.val := fun h => hc₂h₁ (Fin.ext h)
  have a₅ : c₂.val ≠ h₂.val := fun h => hc₂h₂ (Fin.ext h)
  have a₆ : h₁.val ≠ h₂.val := fun h => hh (Fin.ext h)
  have a₇ : x.val ≠ h₁.val := fun h => hxh₁ (Fin.ext h)
  have a₈ : x.val ≠ h₂.val := fun h => hxh₂ (Fin.ext h)
  by_contra hn
  have n₁ : x.val ≠ c₁.val := fun h => hn (Or.inl (Fin.ext h))
  have n₂ : x.val ≠ c₂.val := fun h => hn (Or.inr (Fin.ext h))
  omega
