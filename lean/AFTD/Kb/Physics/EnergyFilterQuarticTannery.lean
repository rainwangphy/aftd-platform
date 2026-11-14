import AFTD.Prelude

/-!
# energy_filter_quartic_tannery

Topic: statistical_mechanics   Node: 58cfa97d5d2b

Provenance: helper lemma. OP-892: shifted quartic reindexing and dominated convergence.

For an absolutely summable quartic cycle, a uniformly bounded shifted kernel with a common pointwise limit passes through the cycle sum by dominated convergence.
-/

theorem energy_filter_quartic_tannery
    (a : ℤ → ℝ) (K : ℕ → ℤ → ℤ → ℤ → ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (hab : Summable (fun p : ℤ × ℤ × ℤ =>
      |a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)|))
    (hlim : ∀ u v w, Filter.Tendsto (fun k => K k u v w) Filter.atTop (nhds c))
    (hbound : ∀ᶠ k in Filter.atTop, ∀ u v w, |K k u v w| ≤ C) :
    Filter.Tendsto
      (fun k : ℕ => ∑' p : ℤ × ℤ × ℤ,
        (a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)) *
          K k p.1 p.2.1 (p.2.1 - p.2.2))
      Filter.atTop
      (nhds ((∑' p : ℤ × ℤ × ℤ,
        a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)) * c)) := by
  let Q : ℤ × ℤ × ℤ → ℝ := fun p =>
    a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)
  have hQabs : Summable (fun p => |Q p|) := by simpa [Q] using hab
  have hQ : Summable Q := hQabs.of_abs
  have hsum : Summable (fun p => C * |Q p|) := hQabs.mul_left C
  have hpoint : ∀ p : ℤ × ℤ × ℤ,
      Filter.Tendsto (fun k : ℕ => Q p * K k p.1 p.2.1 (p.2.1 - p.2.2))
        Filter.atTop (nhds (Q p * c)) := by
    intro p
    exact tendsto_const_nhds.mul (hlim p.1 p.2.1 (p.2.1 - p.2.2))
  have hbd : ∀ᶠ k : ℕ in Filter.atTop, ∀ p : ℤ × ℤ × ℤ,
      ‖Q p * K k p.1 p.2.1 (p.2.1 - p.2.2)‖ ≤ C * |Q p| := by
    filter_upwards [hbound] with k hk p
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |Q p| * |K k p.1 p.2.1 (p.2.1 - p.2.2)| ≤ |Q p| * C :=
        mul_le_mul_of_nonneg_left (hk p.1 p.2.1 (p.2.1 - p.2.2)) (abs_nonneg _)
      _ = C * |Q p| := mul_comm _ _
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint hbd
  have hs : (∑' p, Q p * c) = (∑' p, Q p) * c := hQ.tsum_mul_right c
  rw [hs] at ht
  exact ht
