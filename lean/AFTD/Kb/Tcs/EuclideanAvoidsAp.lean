import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanHasMonoAp

/-!
# euclidean_avoids_ap

Topic: combinatorics   Node: 42af4296d8ce

Provenance: formalization of a published result. Source: scout/2611-12360-avoiding-short-progressions-in-euclidean-ramsey-theory-ii.md:109

The Euclidean Ramsey avoidance property euclidean_avoids_ap n r α M β (commonly denoted E^n ↛ (α ℓ_r, β ℓ_M)) asserts that there exists a two-coloring c : EuclideanSpace ℝ (Fin n) → Bool containing neither a monochromatic r-term arithmetic progression with spacing α of color false nor a monochromatic M-term arithmetic progression with spacing β of color true.
-/

/-- Two-coloring of Euclidean space avoiding an r-term AP with spacing α in color false and an M-term AP with spacing β in color true. -/
def euclidean_avoids_ap (n : ℕ) (r : ℕ) (α : ℝ) (M : ℕ) (β : ℝ) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin n) → Bool,
    ¬ euclidean_has_mono_ap c r α false ∧ ¬ euclidean_has_mono_ap c M β true
