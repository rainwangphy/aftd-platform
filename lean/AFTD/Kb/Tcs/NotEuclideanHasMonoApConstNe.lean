import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanHasMonoAp

/-!
# not_euclidean_has_mono_ap_const_ne

Topic: combinatorics   Node: 774e3f6185f5

Provenance: helper lemma. folklore

For any dimension n, any positive integer m with 0 < m, and any spacing α : ℝ, the constant coloring c = (fun _ => true) on EuclideanSpace ℝ (Fin n) satisfies ¬ euclidean_has_mono_ap c m α false.
-/

/-- A constant coloring with color true contains no monochromatic arithmetic progression of color false. -/
theorem not_euclidean_has_mono_ap_const_ne {n : ℕ} (m : ℕ) (α : ℝ) (hm : 0 < m) :
    ¬ euclidean_has_mono_ap (fun (_ : EuclideanSpace ℝ (Fin n)) => true) m α false := by
  rintro ⟨x₀, v, -, h⟩
  have h0 := h ⟨0, hm⟩
  cases h0
