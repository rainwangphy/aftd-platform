import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.HedgeConstruction
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# approx_minimax

Topic: equilibria   Node: eefb8d583c5b

Provenance: helper lemma. TCSlib, `approx_minimax`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/FiniteMinimax.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Approximate minimax for finite zero-sum games. Let $G$ be a finite two-player zero-sum game with payoff matrix $A$, having $M \ge 2$
row actions and at least one column action, and let $\varepsilon > 0$. Then there exist
a mixed row strategy $p$ and a mixed column strategy $q$ that form an
$\varepsilon$-approximate saddle point: for every pure row $i$ and every pure column
$j$,
\[
  \sum_{k} p_k\, A_{kj} \;+\; \varepsilon \;\ge\; \sum_{\ell} A_{i\ell}\, q_\ell .
\]
That is, up to an additive $\varepsilon$, the expected payoff of $p$ against any pure
column is at least the expected payoff of any pure row against $q$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The approximate minimax theorem for finite zero-sum games: for any game `G` with at least two row actions and any `ε > 0`, there exist a row mixed strategy `p` and a column mixed strategy `q` forming an ε-approximate saddle point, i.e. `payoffVsPure G p j + ε ≥ pureVsPayoff G i q` for all pure rows `i` and columns `j`. [CBL06, Thm 7.1 (finite case, i.e. von Neumann's minimax theorem)]; [FS99, §5 (proof of the minmax theorem), §6.1 (approximate minimax via multiplicative weights)]. Deviation: the sources state the exact minimax equality (or an `O(√(log M / T))` rate); here the conclusion is an ε-approximate saddle point with the explicit parameter choice `η = min 1 (4ε/5)` and `T = ⌈2 log M / (η ε)⌉ + 1`, and the hypothesis `1 < M` (Hedge needs at least two experts; it makes `log M > 0`) is carried from the Hedge bound. The exact finite value is derived in `Minimax.ConvexMinimaxCore.finite_minimax_value`. **Proof sketch.** Step 1: choose the learning rate `η := min 1 (4ε/5)`, so `0 < η ≤ 4ε/5`. Step 2: choose the horizon `T := ⌈2 log M / (η ε)⌉ + 1`, so that `T > 0` and `log M / (η T) ≤ ε/2`. Step 3: apply `hedge_construction` with these parameters to get `p`, `q` with error `(log M / η + η T / 8) / T`. Step 4: this error splits as `log M / (η T) + η / 8 ≤ ε/2 + ε/10 ≤ ε`, which gives the claim. -/
theorem approx_minimax {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (hM : 1 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (p : MixedStrategy M) (q : MixedStrategy N),
      ∀ (i : Fin M) (j : Fin N),
        payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  -- Choose `η` and `T` so the explicit error
  -- `(log M / η + ηT / 8) / T` from `hedge_construction` is at most `ε`.
  -- With the tight bound, regret/T ≤ (log M)/(ηT) + η/8.
  have hM_pos : (1 : ℝ) < ↑M := by exact_mod_cast hM
  have hlogM_pos : 0 < Real.log (↑M) := Real.log_pos hM_pos
  -- Step 1: choose η = min 1 (4 * ε / 5)
  set η := min 1 (4 * ε / 5)
  have hη_pos : 0 < η := lt_min one_pos (by linarith)
  have hη_le_ε : η ≤ 4 * ε / 5 := min_le_right _ _
  -- Step 2: choose T large enough that (log M)/(η * T) ≤ ε/2
  -- i.e., T ≥ 2 * log M / (η * ε)
  obtain ⟨T, hT_pos, hT_large⟩ : ∃ T : ℕ, 0 < T ∧
      Real.log ↑M / (η * ↑T) ≤ ε / 2 := by
    -- T = ⌈2 * log M / (η * ε)⌉ + 1 works
    refine ⟨⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have hηT_pos : 0 < η * ↑(⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1) :=
      mul_pos hη_pos (by exact_mod_cast Nat.succ_pos _)
    rw [div_le_iff₀ hηT_pos]
    set T' := ⌈2 * Real.log ↑M / (η * ε)⌉₊ + 1
    have hT'_ge : (T' : ℝ) ≥ 2 * Real.log ↑M / (η * ε) := by
      have : (⌈2 * Real.log ↑M / (η * ε)⌉₊ : ℝ) ≥ 2 * Real.log ↑M / (η * ε) :=
        Nat.le_ceil _
      simp only [T', Nat.cast_add, Nat.cast_one]
      linarith
    calc Real.log ↑M
        = ε / 2 * (η * (2 * Real.log ↑M / (η * ε))) := by field_simp
      _ ≤ ε / 2 * (η * ↑T') := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hT'_ge.le (le_of_lt hη_pos)
  -- Step 3: run the Hedge construction with these parameters.
  obtain ⟨p, q, hpq⟩ := hedge_construction G hM T hT_pos η hη_pos
  exact ⟨p, q, fun i j => by
    have hbound := hpq i j
    -- Step 4: show the error is at most ε: (log M / η + η * T / 8) / T ≤ ε
    suffices hle : (Real.log ↑M / η + η * ↑T / 8) / ↑T ≤ ε by linarith
    have hT_pos_r : (0 : ℝ) < ↑T := Nat.cast_pos.mpr hT_pos
    rw [add_div, div_div]
    -- First term: log M / (η * T) ≤ ε/2
    -- Second term: η * T / 8 / T = η / 8 ≤ (4ε/5) / 8 = ε/10
    have h1 := hT_large
    have h2 : η * ↑T / 8 / ↑T = η / 8 := by
      field_simp
    rw [h2]
    have h3 : η / 8 ≤ ε / 2 := by
      calc η / 8 ≤ (4 * ε / 5) / 8 := by linarith [hη_le_ε]
        _ = ε / 10 := by ring
        _ ≤ ε / 2 := by linarith
    linarith⟩
