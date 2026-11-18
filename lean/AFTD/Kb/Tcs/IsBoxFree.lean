import AFTD.Prelude

/-!
# is_box_free

Topic: combinatorics   Node: adb2f269c825

Provenance: formalization of a published result. Source: arXiv:2611.19635, Section 1

A 2-coloring f : Fin a → Fin b → Fin c → Bool of the 3D grid [a] × [b] × [c] is box-free if no 2 × 2 × 2 subgrid (box) s × t × u (with |s| = 2, |t| = 2, |u| = 2) is monochromatic under f.
-/

/-- Predicate that a 2-coloring of an a × b × c grid contains no monochromatic axis-parallel box. -/
def is_box_free {a b c : ℕ} (f : Fin a → Fin b → Fin c → Bool) : Prop := ∀ (s : Finset (Fin a)) (t : Finset (Fin b)) (u : Finset (Fin c)),
  s.card = 2 → t.card = 2 → u.card = 2 → ¬ ∃ col : Bool, ∀ x ∈ s, ∀ y ∈ t, ∀ z ∈ u, f x y z = col
