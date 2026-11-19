import AFTD.Prelude

/-!
# triangle_common_color_cannot_be_hidden_on_matching_port

Topic: combinatorics   Node: bbbe5eab9fa7

Provenance: helper lemma. Triangle-interface propagation in the OP-874 campaign.

A color present at all three local triangle states cannot be hidden at a matching port when exposed colors agree across the triangle edges.
-/

theorem triangle_common_color_cannot_be_hidden_on_matching_port
    {Ω : Type*} (z m x y n u v p : Ω)
    (h1 : z = x ∨ z = y ∨ z = n) (h2 : z = u ∨ z = v ∨ z = p)
    (hmy : m ≠ y) (hmn : m ≠ n) (hmv : m ≠ v) (hmp : m ≠ p)
    (hxu : x ≠ u) : m ≠ z := by
  aesop
