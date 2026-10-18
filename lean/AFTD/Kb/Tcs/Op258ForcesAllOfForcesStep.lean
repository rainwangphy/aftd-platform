import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_258_forces_all_of_forces_step

Topic: combinatorics   Node: 86a5142a6885

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

Assume that for every positive antitone profile a with Σ a i > 1 and every k ≥ 3, forcing a monochromatic K_k implies forcing a monochromatic K_{k+1}. Then for every such a, if a forces a monochromatic K_3, it forces a monochromatic K_k for every k ≥ 3.
-/

/-- Assembly: once the successor step is available for every k ≥ 3, the target's k = 3 hypothesis propagates to all k ≥ 3 by `Nat.le_induction`. -/
theorem op_258_forces_all_of_forces_step
    (step : ∀ (a : ℕ+ → ℝ), (∀ i, 0 < a i) → Antitone a → 1 < ∑' i : ℕ+, ENNReal.ofReal (a i) →
      ∀ k : ℕ, 3 ≤ k → op_258_forces a k → op_258_forces a (k + 1))
    (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (hsum : 1 < ∑' i : ℕ+, ENNReal.ofReal (a i)) (h3 : op_258_forces a 3) :
    ∀ k ≥ 3, op_258_forces a k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h3
  | succ m hm ih => exact step a hpos hanti hsum m hm ih
