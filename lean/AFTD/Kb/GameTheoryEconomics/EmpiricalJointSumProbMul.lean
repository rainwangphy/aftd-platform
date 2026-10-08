import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistribution
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal

/-!
# empiricalJoint_sum_prob_mul

Topic: equilibria   Node: 6226b6048705

Provenance: helper lemma. TCSlib, `empiricalJoint_sum_prob_mul`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Averaging a payoff against the empirical joint distribution. Fix $T > 0$ rounds of play in which, in round $t$, the row player uses a mixed strategy
$p_t$ over $\mathrm{Fin}\,M$ and the column player a mixed strategy $q_t$ over
$\mathrm{Fin}\,N$; write $(p_t)_i$ and $(q_t)_j$ for the weights placed on actions $i$
and $j$. Let $\sigma$ be the empirical joint distribution, whose value at each profile
$(i,j)$ is the time average $\sigma_{ij} = \frac{1}{T}\sum_{t=1}^{T} (p_t)_i\,(q_t)_j$.
Then for every function $f : \mathrm{Fin}\,M \times \mathrm{Fin}\,N \to \bbr$,
\[
\sum_{i}\sum_{j} \sigma_{ij}\, f(i,j) \;=\; \frac{1}{T}\sum_{t=1}^{T}\sum_{i}\sum_{j}
(p_t)_i\,(q_t)_j\, f(i,j).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- Any utility-style sum `Σ_i Σ_j σ(i, j) · f(i, j)` over the empirical joint distribution `σ = empiricalJoint hT p q` equals the time average `(1/T) Σ_t Σ_i Σ_j p_t(i) q_t(j) f(i, j)` of the per-round expected values of `f`. **Proof sketch.** Bookkeeping only: for each profile, move the factor `f i j` inside the time sum (`hStep`); pull the division by `T` out of the double sum over profiles; then swap the order of summation so time is outermost (two applications of `Finset.sum_comm`). -/
lemma empiricalJoint_sum_prob_mul {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (f : Fin M → Fin N → ℝ) :
    (∑ i : Fin M, ∑ j : Fin N,
        (empiricalJoint hT p q).prob i j * f i j) =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * f i j) / T := by
  -- This lemma is only bookkeeping: pull the division by `T` out of the finite
  -- sums, then swap the order of the time/action sums.
  show ∑ i : Fin M, ∑ j : Fin N,
        (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) * f i j =
       (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * f i j) / (T : ℝ)
  have hStep : ∀ i : Fin M, ∀ j : Fin N,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) * f i j =
        (∑ t : Fin T, (p t).weights i * (q t).weights j * f i j) /
          (T : ℝ) := by
    intro i j
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [show (∑ i : Fin M, ∑ j : Fin N,
            (∑ t : Fin T, (p t).weights i * (q t).weights j * f i j) /
              (T : ℝ))
      = (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
            (p t).weights i * (q t).weights j * f i j) / (T : ℝ) from ?_]
  · congr 1
    rw [show (∑ i : Fin M, ∑ j : Fin N, ∑ t : Fin T,
              (p t).weights i * (q t).weights j * f i j)
        = (∑ i : Fin M, ∑ t : Fin T, ∑ j : Fin N,
              (p t).weights i * (q t).weights j * f i j) from
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
    exact Finset.sum_comm
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_div]
