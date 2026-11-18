import AFTD.Prelude

/-!
# grid_box_free

Topic: combinatorics   Node: b9a19779e7ef

Provenance: formalization of a published result. Source: arXiv:2611.19635 (Constructive and computational methods for extremal and near-extremal box colorings), Sec. 1

A 2-coloring $f : [a] \times [b] \times [c] \to \{0, 1\}$ is box-free if for all $x_1 < x_2 \le a$, $y_1 < y_2 \le b$, and $z_1 < z_2 \le c$, the eight vertices $\{x_1, x_2\} \times \{y_1, y_2\} \times \{z_1, z_2\}$ are not all monochromatic under $f$.
-/

/-- A 2-coloring of [a] × [b] × [c] is box-free if no axis-parallel box is monochromatic. -/
def grid_box_free {a b c : ℕ} (f : Fin a → Fin b → Fin c → Bool) : Prop := ∀ (x₁ x₂ : Fin a) (y₁ y₂ : Fin b) (z₁ z₂ : Fin c),
    x₁ < x₂ → y₁ < y₂ → z₁ < z₂ →
      ¬ (f x₁ y₁ z₁ = f x₁ y₂ z₁ ∧
         f x₁ y₁ z₁ = f x₂ y₁ z₁ ∧
         f x₁ y₁ z₁ = f x₂ y₂ z₁ ∧
         f x₁ y₁ z₁ = f x₁ y₁ z₂ ∧
         f x₁ y₁ z₁ = f x₁ y₂ z₂ ∧
         f x₁ y₁ z₁ = f x₂ y₁ z₂ ∧
         f x₁ y₁ z₁ = f x₂ y₂ z₂)
