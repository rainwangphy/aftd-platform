import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.Potential

/-!
# log_potential_telescope

Topic: learning   Node: 8b860ac2ece5

Provenance: helper lemma. TCSlib, `log_potential_telescope`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Telescoping of the log potential. Let $\eta \in \bbr$ and let $\ell$ be a loss sequence for $N$ experts over $T$ rounds,
with potential $W_t =  potential\ \eta\ \ell\ t$.  Then the one-step changes of the
log potential telescope:
\[
  \sum_{t=0}^{T-1} \bigl(\log W_{t+1} - \log W_t\bigr) \;=\; \log W_T - \log W_0 .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Telescoping the one-step changes of the log potential: summing `log W_{t+1} - log W_t` over the `T` rounds gives `log W_T - log W_0`. Pure bookkeeping (the sum over `Fin T` is rewritten as a sum over `range T` and `Finset.sum_range_sub` applies); no textbook counterpart. -/
lemma log_potential_telescope {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) :
    ∑ t : Fin T, (Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)) =
      Real.log (potential η ℓ T) - Real.log (potential η ℓ 0) := by
  set f := fun n => Real.log (potential η ℓ n)
  show ∑ t : Fin T, (f (t.val + 1) - f t.val) = f T - f 0
  conv_lhs => arg 2; ext t; rw [show t.val = (t : ℕ) from rfl]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n)]
  exact Finset.sum_range_sub f T
