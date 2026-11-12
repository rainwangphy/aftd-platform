import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanHasMonoAp

/-!
# euclidean_has_mono_ap_of_le

Topic: combinatorics   Node: 942397e96ef8

Provenance: helper lemma. folklore

For any dimension n, coloring c : EuclideanSpace ℝ (Fin n) → Bool, spacings α, color b, and lengths m₁ ≤ m₂, if c contains a monochromatic m₂-term arithmetic progression of color b with spacing α, then it also contains a monochromatic m₁-term arithmetic progression of color b with spacing α.
-/

/-- If a coloring contains a monochromatic arithmetic progression of length m₂, it also contains one of length m₁ for m₁ ≤ m₂. -/
theorem euclidean_has_mono_ap_of_le {n : ℕ} {c : EuclideanSpace ℝ (Fin n) → Bool}
    {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) (α : ℝ) (b : Bool)
    (h : euclidean_has_mono_ap c m₂ α b) : euclidean_has_mono_ap c m₁ α b := by
  rcases h with ⟨x₀, v, hv, hc⟩
  exact ⟨x₀, v, hv, fun k => hc ⟨k.val, k.isLt.trans_le hle⟩⟩
