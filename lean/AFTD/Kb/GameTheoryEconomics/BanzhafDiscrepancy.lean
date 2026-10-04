import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PropensityBanzhafIndex

/-!
# banzhaf_discrepancy

Topic: general_equilibrium   Node: c131945125af

The discrepancy of weights w for a target power distribution m: the l1 distance between m and the p-propensity Banzhaf index of (w; q).
-/

/-- The discrepancy of weights `w` for target `m` (How Banzhaf Makes a Victor, Sec. 2.3): the `ℓ₁` distance between `m` and the `p`-propensity Banzhaf index of `(w; q)`. -/
noncomputable def banzhaf_discrepancy {n : ℕ} (m : Fin n → ℝ) (p q : ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ i, |m i - propensity_banzhaf_index p q w i|
