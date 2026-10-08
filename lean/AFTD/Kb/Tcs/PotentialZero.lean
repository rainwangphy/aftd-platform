import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLoss
import AFTD.Kb.Tcs.HedgeWeight
import AFTD.Kb.Tcs.Potential

/-!
# potential_zero

Topic: learning   Node: ed1703b46f38

Provenance: helper lemma. TCSlib, `potential_zero`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Initial value of the potential. Fix $N \ge 1$ experts, a horizon $T$, and a loss sequence $\ell$ over these experts and
rounds, and let $\eta \in \bbr$ be a learning rate. At time $0$ every expert has zero
cumulative loss, so each unnormalized Hedge weight equals $1$, and the potential is
\[
  W_0 \;=\; \sum_{i=1}^{N} \exp\!\bigl(-\eta \cdot L_0(i)\bigr) \;=\; N .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The potential at time `0` equals `N`: every cumulative loss is `0`, so every weight is `1`. -/
lemma potential_zero {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) :
    potential η ℓ 0 = N := by
  simp only [potential, hedgeWeight, cumLoss]
  have hfilt : ∀ i : Fin N, ((Finset.univ (α := Fin T)).filter (fun s => s.val < 0)).sum
      (fun s => ℓ s i) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro s hs
    simp at hs
  simp only [hfilt, mul_zero, exp_zero, Finset.sum_const, Finset.card_fin]
  simp
