import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EmpiricalStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# pureVsPayoff_empiricalStrategy

Topic: equilibria   Node: e278f8bc7f2f

Provenance: helper lemma. TCSlib, `pureVsPayoff_empiricalStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pure-row payoff against the empirical column strategy. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N \ge 1$ column
actions, and payoff matrix $A$. Fix a row action $i$ and a sequence of column actions
$a_0, \dots, a_{T-1}$ with $T > 0$, and let $\hat{q}$ be the associated empirical column
strategy. Then the expected payoff of row $i$ against $\hat{q}$ equals the average
payoff over the sequence:
\[
  \sum_{j} A_{ij}\,\hat{q}_j \;=\; \frac{1}{T}\sum_{t=0}^{T-1} A_{i,\,a_t}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The payoff of a pure row `i` against the empirical column strategy of a sequence of played columns equals the time average `(1/T) Σ_t A(i, j_t)` of the payoffs of `i` against the columns actually played. [FS99, §5]. **Proof sketch.** A four-step `calc`: unfold the empirical weights and push the payoff `A(i, x)` inside the indicator sum for each column `x`; pull the division by `T` out of the outer sum; swap the order of summation so time is outermost; for each round `t` collapse the indicator sum over columns `x` to the single term `x = j_t`. -/
lemma pureVsPayoff_empiricalStrategy {M N T : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (hT : 0 < T) (actions : Fin T → Fin N) (i : Fin M) :
    pureVsPayoff G i (empiricalStrategy hT actions) =
      (∑ t : Fin T, G.payoff i (actions t)) / T := by
  simp only [pureVsPayoff, empiricalStrategy]
  calc ∑ x : Fin N, G.payoff i x * ((∑ t : Fin T, if actions t = x then 1 else 0) / ↑T)
      -- Step 1: push the payoff inside the indicator sum.
      = ∑ x : Fin N, (∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          congr 1
          ext x
          rw [← Finset.mul_sum]
          ring
      -- Step 2: pull the division by `T` out of the column sum.
    _ = (∑ x : Fin N, ∑ t : Fin T, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_div]
      -- Step 3: swap the order of summation.
    _ = (∑ t : Fin T, ∑ x : Fin N, G.payoff i x *
            (if actions t = x then 1 else 0)) / ↑T := by
          rw [Finset.sum_comm]
      -- Step 4: collapse each indicator sum to the played column.
    _ = (∑ t : Fin T, G.payoff i (actions t)) / ↑T := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_eq_single (actions t)]
          · simp
          · intro b _ hb
            simp [hb.symm]
          · intro h
            exact False.elim (h (Finset.mem_univ _))
