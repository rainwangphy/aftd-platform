import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AverageStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# payoffVsPure_averageStrategy

Topic: equilibria   Node: 6af54355a79d

Provenance: helper lemma. TCSlib, `payoffVsPure_averageStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Average strategy's payoff against a pure column. Let $G$ be a finite two-player zero-sum game with $M \ge 1$ row actions and $N$ column
actions, given by a payoff matrix $A$ with $0 \le A_{ij} \le 1$, and fix a pure column
action $j$. Let $T > 0$ and let $p_0, \dots, p_{T-1}$ be probability distributions over
the $M$ row actions, each presented as non-negative weights $p_t(i)$ summing to $1$, and
let $\bar{p}$ be their average strategy, the mixed row strategy with weights $\bar{p}_i
= \frac{1}{T}\sum_{t=0}^{T-1} p_t(i)$. Then the expected payoff of $\bar{p}$ against
column $j$ satisfies
\[
  \sum_{i} \bar{p}_i \, A_{ij}
  \;=\;
  \frac{1}{T} \sum_{t=0}^{T-1} \sum_{i} p_t(i) \, A_{ij}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The payoff of the averaged row strategy against a pure column `j` equals the time average of the per-round payoffs `Σ_i strategies t i · A(i, j)` against that column. [FS99, §5]. -/
lemma payoffVsPure_averageStrategy {M N T : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (hT : 0 < T)
    (strategies : Fin T → Fin M → ℝ)
    (h_nonneg : ∀ t i, 0 ≤ strategies t i)
    (h_sum : ∀ t, ∑ i : Fin M, strategies t i = 1)
    (j : Fin N) :
    payoffVsPure G (averageStrategy hT strategies h_nonneg h_sum) j =
      (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / T := by
  simp only [payoffVsPure, averageStrategy]
  calc ∑ x : Fin M, (∑ t : Fin T, strategies t x) / ↑T * G.payoff x j
      = ∑ x : Fin M, (∑ t : Fin T, strategies t x * G.payoff x j) / ↑T := by
          congr 1
          ext x
          rw [← Finset.sum_mul]
          ring
    _ = (∑ x : Fin M, ∑ t : Fin T, strategies t x * G.payoff x j) / ↑T := by
          rw [Finset.sum_div]
    _ = (∑ t : Fin T, ∑ i : Fin M, strategies t i * G.payoff i j) / ↑T := by
          rw [Finset.sum_comm]
