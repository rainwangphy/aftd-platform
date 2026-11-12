import AFTD.Prelude

/-!
# euclidean_has_mono_ap

Topic: combinatorics   Node: c856bedb9e29

Provenance: formalization of a published result. Source: scout/2611-12360-avoiding-short-progressions-in-euclidean-ramsey-theory-ii.md:104

For a dimension n, a two-coloring c : EuclideanSpace ℝ (Fin n) → Bool, a term count m : ℕ, a spacing α : ℝ, and a color b : Bool, euclidean_has_mono_ap c m α b holds if there exist a base point x₀ and a difference vector v in EuclideanSpace ℝ (Fin n) with ‖v‖ = α such that c (x₀ + (k : ℝ) • v) = b for all k : Fin m.
-/

/-- A coloring of Euclidean space contains a monochromatic arithmetic progression of a given color and spacing. -/
def euclidean_has_mono_ap {n : ℕ} (c : EuclideanSpace ℝ (Fin n) → Bool)
    (m : ℕ) (α : ℝ) (b : Bool) : Prop :=
  ∃ (x₀ v : EuclideanSpace ℝ (Fin n)), ‖v‖ = α ∧ ∀ k : Fin m, c (x₀ + (k : ℝ) • v) = b
