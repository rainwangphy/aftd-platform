import AFTD.Prelude

/-!
# is_pseudometric

Topic: algorithms   Node: 4ee0b9548e42

Provenance: formalization of a published result. Source: arXiv:2610.23032 Section 4

For an arbitrary type V and function d : V → V → ℝ, d is a pseudometric if d(u, u) = 0 for all u : V, d(u, v) = d(v, u) for all u, v : V, and d(u, w) ≤ d(u, v) + d(v, w) for all u, v, w : V.
-/

/-- A pseudometric satisfies reflexivity, symmetry, and the triangle inequality. -/
def is_pseudometric {V : Type*} (d : V → V → ℝ) : Prop :=
  (∀ u, d u u = 0) ∧ (∀ u v, d u v = d v u) ∧ (∀ u v w, d u w ≤ d u v + d v w)
