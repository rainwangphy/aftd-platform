import AFTD.Prelude
import AFTD.Kb.Tcs.MonotoneMixtureWeight
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# monotoneMixtureWeight_nonneg

Topic: information   Node: 52eb90cce18e

Provenance: helper lemma. arXiv:2610.01563 Lemma 3 (1)

If $P : \mathbb{N}^+ \to \mathbb{R}$ is antitone (nonincreasing), then the mixture weight $w_k = k(P(k) - P(k+1))$ is nonnegative for every $k \in \mathbb{N}^+$.
-/

/-- Nonnegativity of mixture weights for an antitone distribution. -/
lemma monotoneMixtureWeight_nonneg (P : ℕ+ → ℝ) (h_anti : Antitone P) (k : ℕ+) :
    0 ≤ monotoneMixtureWeight P k :=
  mul_nonneg (Nat.cast_nonneg (k : ℕ)) (sub_nonneg.mpr (h_anti (Nat.le_add_right (k : ℕ) 1)))
