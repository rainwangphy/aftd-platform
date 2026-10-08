import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# averageStrategy

Topic: equilibria   Node: 7763023ad5d8

Provenance: formalization of a published result. Source: TCSlib, `averageStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given $T$ distributions $p_0, \dots, p_{T-1}$ over $\mathrm{Fin}\,n$ (each
presented as non-negative weights summing to $1$) and $T > 0$, the
\emph{average strategy} is the mixed strategy with weights
\[
  \bar{p}_i \;=\; \frac{1}{T} \sum_{t=0}^{T-1} p_t(i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The time average of `T > 0` probability distributions over `n` actions, as a mixed strategy: the weight of action `i` is `(1/T) Σ_t strategies t i`. This packages the averaged row strategy `P̄ = (1/T) Σ_t P_t` used after running Hedge for `T` rounds. [FS99, §5]. -/
noncomputable def averageStrategy {n T : ℕ} [NeZero n] (hT : 0 < T)
    (strategies : Fin T → Fin n → ℝ)
    (h_nonneg : ∀ t i, 0 ≤ strategies t i)
    (h_sum : ∀ t, ∑ i : Fin n, strategies t i = 1) : MixedStrategy n where
  weights i := (∑ t : Fin T, strategies t i) / T
  nonneg i := div_nonneg (Finset.sum_nonneg fun t _ => h_nonneg t i) (Nat.cast_nonneg T)
  sum_one := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [h_sum, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
