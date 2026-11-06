import AFTD.Prelude

/-!
# diagram_horizontal_slide_box

Topic: combinatorics   Node: f3b097366bfd

Provenance: formalization of a published result. Source: arXiv:2611.07715, Definition 3.4(2)

For $D : \text{Finset } (\mathbb{N} \times \mathbb{N})$, $b_1, b_2, x \in \mathbb{N} \times \mathbb{N}$, and $c = (b_2.1, b_1.2)$, `diagram_horizontal_slide_box D b_1 b_2 x` returns $c$ if $x = b_2$; $(x.1, x.2 + 1)$ if $c \in D.erase b_2$, $x \in D.erase b_2$, $x.1 \ge b_2.1$, and $x.2 \ge b_1.2$; and $x$ otherwise.
-/

/-- The box mapping under the horizontal slide of an admissible pair. -/
def diagram_horizontal_slide_box (D : Finset (ℕ × ℕ)) (b₁ b₂ : ℕ × ℕ) (x : ℕ × ℕ) : ℕ × ℕ := let r := b₂.1; let q := b₁.2; let c := (r, q); let c_in_D'' := c ∈ D.erase b₂; if x = b₂ then c else if c_in_D'' ∧ x ∈ D.erase b₂ ∧ x.1 ≥ r ∧ x.2 ≥ q then (x.1, x.2 + 1) else x
