import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanAvoidsAp
import AFTD.Kb.Tcs.EuclideanHasMonoApOfLe
import AFTD.Kb.Tcs.EuclideanHasMonoAp

/-!
# euclidean_avoids_ap_of_le

Topic: combinatorics   Node: 079fc30d6aed

Provenance: helper lemma. folklore

For any dimension n, natural numbers r₁ ≤ r₂ and M₁ ≤ M₂, and spacings α, β : ℝ, if euclidean_avoids_ap n r₁ α M₁ β holds, then euclidean_avoids_ap n r₂ α M₂ β holds.
-/

/-- Monotonicity of Euclidean AP avoidance: avoiding shorter progressions implies avoiding longer progressions. -/
theorem euclidean_avoids_ap_of_le {n : ℕ} {r₁ r₂ M₁ M₂ : ℕ} (hr : r₁ ≤ r₂) (hM : M₁ ≤ M₂)
    {α β : ℝ} (h : euclidean_avoids_ap n r₁ α M₁ β) : euclidean_avoids_ap n r₂ α M₂ β := by
  rcases h with ⟨c, hr1, hM1⟩
  refine ⟨c, ?_, ?_⟩
  · intro h2
    exact hr1 (euclidean_has_mono_ap_of_le hr α false h2)
  · intro h2
    exact hM1 (euclidean_has_mono_ap_of_le hM β true h2)
