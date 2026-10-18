import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.Tcs.Op258HasMonoClique

/-!
# op_258_forces_mono_bound

Topic: combinatorics   Node: 54a4903cfa9d

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

If b ≤ a pointwise and a forces a monochromatic K_k, then b forces a monochromatic K_k.
-/

/-- Forcing is antitone in the decay profile: shrinking the bound only removes colourings, so it cannot destroy forcing. -/
theorem op_258_forces_mono_bound {a b : ℕ+ → ℝ} (hba : ∀ i, b i ≤ a i) {k : ℕ}
    (hk : op_258_forces a k) : op_258_forces b k := by
  rcases hk with ⟨n₀, hn₀⟩
  refine ⟨n₀, fun n hn c hc => hn₀ n hn c fun i => ?_⟩
  have hbc := hc i
  have h_le : b i * (n.choose 2 : ℝ) ≤ a i * (n.choose 2 : ℝ) := by
    gcongr
    exact hba i
  exact le_trans hbc h_le
