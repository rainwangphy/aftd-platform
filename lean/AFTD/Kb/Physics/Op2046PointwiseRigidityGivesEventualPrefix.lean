import AFTD.Prelude

/-!
# op2046_pointwise_rigidity_gives_eventual_prefix

Topic: quantum_mechanics   Node: c9996b0785c6

Provenance: helper lemma. OP-2046 candidate Airy persistence: global point rigidity and the standard Cesaro averaging theorem.

If a real sequence converges to zero, then adding any positive linear drift to its prefix sums makes them eventually strictly positive.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_pointwise_rigidity_gives_eventual_prefix
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ k : ℕ in atTop, 0 < (∑ j ∈ Finset.range k, u j) + (k : ℝ) * s := by
  have hmean : ∀ᶠ k : ℕ in atTop, -s < (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j :=
    hu.cesaro.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hmean, eventually_ge_atTop 1] with k hk hkpos
  have hkp : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [inv_mul_eq_div] at hk
  have hh := (lt_div_iff₀ hkp).mp hk
  nlinarith
