import AFTD.Prelude

/-!
# diagram_vertical_slide_box

Topic: combinatorics   Node: 3d2ee6d2c723

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.4(1)

For $D : \text{Finset } (\mathbb{N} \times \mathbb{N})$, $b_1, b_2, x \in \mathbb{N} \times \mathbb{N}$, and $c = (b_2.1, b_1.2)$, `diagram_vertical_slide_box D b_1 b_2 x` returns $c$ if $x = b_1$; $(x.1 + 1, x.2)$ if $c \in D.erase b_1$, $x \in D.erase b_1$, $x.1 \ge b_2.1$, and $x.2 \ge b_1.2$; and $x$ otherwise.
-/

/-- The box mapping under the vertical slide of an admissible pair. -/
def diagram_vertical_slide_box (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) (x : ℕ × ℕ) : ℕ × ℕ := let r := b₂.1; let q := b₁.2; let c := (r, q); let c_in_D' := c ∈ D.erase b₁; if x = b₁ then c else if c_in_D' ∧ x ∈ D.erase b₁ ∧ x.1 ≥ r ∧ x.2 ≥ q then (x.1 + 1, x.2) else x
