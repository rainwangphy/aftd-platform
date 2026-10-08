import AFTD.Prelude

/-!
# jl_failure_bound_of_dim

Topic: concentration   Node: c038415d2d75

Provenance: helper lemma. TCSlib, `jl_failure_bound_of_dim`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Numerical failure-probability bound for Johnson–Lindenstrauss. Let $\varepsilon > 0$ and let $n \ge 2$ be an integer, and suppose the target dimension
$k$ satisfies $k \ge 32 \log n / \varepsilon^2$. Then for any finite set $V$ of points
in a Euclidean space with $\abs{V} \le n$, one has $k > 0$ and \[ \abs{V}^2 \cdot
2\exp\!\left(-\tfrac{k\varepsilon^2}{8}\right) < 1. \]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- Numerical bookkeeping common to both headline JL theorems. Given the JL dimension hypothesis `k ≥ 32·log n / ε²` together with `V.card ≤ n` and the basic positivity hypotheses on `ε` and `n`, derives: * `0 < k` (so the random matrix has nonzero rows), and * `(V.card)² · 2 · exp(−kε²/8) < 1` (the union-bound failure probability is strictly less than `1`, which is exactly what `johnson_lindenstrauss_of_gaussian` / `_of_subgaussian` consume). The constant `32` is chosen so that `|V|² · 2 · exp(−kε²/8) ≤ 1/2`, keeping the calculation clean. Tighter constants ([DG03, Thm 2.1] gets `4 (ε²/2 − ε³/3)⁻¹`) work but make the bookkeeping noisier. **Proof sketch.** Step (a): from `k ≥ 32 ln n/ε²` deduce `kε²/8 ≥ 4 ln n`. Step (b): since `ln n > 0` this forces `k > 0`. Step (c): `exp(−kε²/8) ≤ exp(−4 ln n) = n⁻⁴`. Step (d): `|V|² · 2 · exp(−kε²/8) ≤ n² · 2 · n⁻⁴ = 2/n² ≤ 1/2 < 1` using `|V| ≤ n` and `n ≥ 2`. -/
lemma jl_failure_bound_of_dim
    (ε : ℝ) (hε_pos : 0 < ε)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    0 < k ∧ (V.card : ℝ) ^ 2 *
        (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_ge_2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog_n_pos : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hε_sq_pos : 0 < ε ^ 2 := by positivity
  -- Step (a): kε²/8 ≥ 4 log n.
  have hk_lb : 4 * Real.log n ≤ (k : ℝ) * ε ^ 2 / 8 := by
    have := (div_le_iff₀ hε_sq_pos).mp hk
    nlinarith
  -- Step (b): 0 < k.
  have hk_real_pos : 0 < (k : ℝ) := by
    have : 0 < (k : ℝ) * ε ^ 2 / 8 :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * Real.log n) hk_lb
    nlinarith
  have hk_pos : 0 < k := by exact_mod_cast hk_real_pos
  -- Step (c): exp(-kε²/8) ≤ n^{-4}.
  have hexp_bound : Real.exp (-(k : ℝ) * ε ^ 2 / 8) ≤ (n : ℝ) ^ (-(4 : ℤ)) := by
    have h1 : -(k : ℝ) * ε ^ 2 / 8 ≤ -(4 * Real.log n) := by linarith
    calc Real.exp (-(k : ℝ) * ε ^ 2 / 8)
        ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (Real.log n * (-(4 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ (-(4 : ℝ)) := by rw [Real.rpow_def_of_pos hn_pos]
      _ = (n : ℝ) ^ (-(4 : ℤ)) := by
          rw [show (-(4 : ℝ)) = ((-(4 : ℤ) : ℤ) : ℝ) from by norm_cast]
          rw [← Real.rpow_intCast]
  -- Step (d): V.card² · 2 · exp(-kε²/8) ≤ 2/n² ≤ 1/2 < 1.
  have hFail : (V.card : ℝ) ^ 2 *
      (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
    have hcard_sq_le : (V.card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hcard_nn : (0 : ℝ) ≤ V.card := by positivity
      have hcard_le : (V.card : ℝ) ≤ n := by exact_mod_cast hV
      exact pow_le_pow_left₀ hcard_nn hcard_le 2
    have h1 : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
            ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := by
      have hrhs_nn : 0 ≤ 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by positivity
      exact mul_le_mul hcard_sq_le
        (mul_le_mul_of_nonneg_left hexp_bound (by norm_num : (0 : ℝ) ≤ 2))
        hrhs_nn (by positivity)
    have h2 : (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) = 2 / (n : ℝ) ^ 2 := by
      rw [_root_.zpow_neg, zpow_ofNat]; field_simp
    have h3 : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
      have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have hn_sq_ge : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hn_sq_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
        ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(4 : ℤ))) := h1
      _ = 2 / (n : ℝ) ^ 2 := h2
      _ ≤ 1 / 2 := h3
      _ < 1 := by norm_num
  exact ⟨hk_pos, hFail⟩
