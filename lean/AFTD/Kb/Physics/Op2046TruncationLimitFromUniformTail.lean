import AFTD.Prelude

/-!
# op2046_truncation_limit_from_uniform_tail

Topic: quantum_mechanics   Node: 1e6082ffc587

Provenance: helper lemma. Uniform-truncation reduction for OP-2046; elementary Cauchy completeness.

If every fixed edge truncation has a limit and its eventual error uniformly tends to zero as the truncation grows, then the full probabilities converge and their limit equals the limit of the truncation probabilities.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_truncation_limit_from_uniform_tail (p e l : ℕ → ℝ) (q : ℕ → ℕ → ℝ) (hq : ∀ k, Tendsto (q k) atTop (𝓝 (l k))) (he : Tendsto e atTop (𝓝 0)) (herr : ∀ k, ∀ᶠ n in atTop, |p n - q k n| ≤ e k) : ∃ a : ℝ, Tendsto p atTop (𝓝 a) ∧ Tendsto l atTop (𝓝 a) := by
  have hp_cauchy : CauchySeq p := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε4 : (0:ℝ) < ε / 4 := by positivity
    have hk_eventually : ∀ᶠ k in atTop, e k < ε / 4 :=
      he.eventually (Iio_mem_nhds hε4)
    obtain ⟨k, hk⟩ := hk_eventually.exists
    have hqk : ∀ᶠ n in atTop, |q k n - l k| < ε / 4 := by
      have h := (Metric.tendsto_atTop.1 (hq k)) (ε/4) hε4
      rw [eventually_atTop]
      obtain ⟨N, hN⟩ := h
      exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
    have hp_bound : ∀ᶠ n in atTop, |p n - l k| < ε / 2 := by
      filter_upwards [herr k, hqk] with n h1 h2
      have htri : |p n - l k| ≤ |p n - q k n| + |q k n - l k| := abs_sub_le _ _ _
      linarith
    obtain ⟨N, hN⟩ := hp_bound.exists_forall_of_atTop
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm' := hN m hm
    have hn' := hN n hn
    rw [Real.dist_eq]
    calc |p m - p n| ≤ |p m - l k| + |l k - p n| := abs_sub_le _ _ _
      _ = |p m - l k| + |p n - l k| := by rw [abs_sub_comm (l k) (p n)]
      _ < ε := by linarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hp_cauchy
  refine ⟨a, ha, ?_⟩
  have hbound : ∀ k, |a - l k| ≤ e k := by
    intro k
    have h1 : Tendsto (fun n => |p n - q k n|) atTop (𝓝 |a - l k|) := (ha.sub (hq k)).abs
    exact le_of_tendsto h1 (herr k)
  have hsub : Tendsto (fun k => l k - a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := e) _ he
    intro k
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hbound k
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hsub.norm
