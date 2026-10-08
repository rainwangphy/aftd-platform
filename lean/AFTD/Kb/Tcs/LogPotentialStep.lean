import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.PotentialPos
import AFTD.Kb.Tcs.PotentialRatioLe

/-!
# log_potential_step

Topic: learning   Node: a65d21d906b4

Provenance: helper lemma. TCSlib, `log_potential_step`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

One-step logarithmic potential bound for Hedge. Fix $N \ge 1$ experts and $T$ rounds, a learning rate $\eta > 0$, and a valid loss
sequence $\ell$, so that $0 \le \ell_t(i) \le 1$ for every round $t$ and expert $i$.
Writing $W_t = \sum_{i=1}^N \exp\!\bigl(-\eta L_t(i)\bigr)$ for the Hedge potential and
$\widehat{\ell}_t = \sum_{i=1}^N p_t(i)\,\ell_t(i)$ for the expected loss under the
Hedge distribution, the one-round change in log-potential is controlled by the expected
loss: for each round $t$,
\[
  \ln W_{t+1} - \ln W_t \;\le\; -\bigl(1 - e^{-\eta}\bigr)\,\widehat{\ell}_t.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- One-step log-potential bound: for a valid loss sequence and `η > 0`, `ln W_{t+1} - ln W_t ≤ -(1 - exp(-η)) · (p_t · ℓ_t)` [CBL06, proof of Thm 2.2]. This is the additive form of `potential_ratio_le`, obtained from `ln x ≤ x - 1`; it is what telescopes over the rounds in `Hedge.Regret`. The hypothesis `ht` is only forwarded to `potential_ratio_le`, which does not use it. -/
lemma log_potential_step {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by
  -- Convert the multiplicative potential-ratio bound into an additive
  -- log-potential bound.  This is what will telescope across time.
  have hWt := potential_pos η ℓ t.val
  have hWt1 := potential_pos η ℓ (t.val + 1)
  rw [← Real.log_div (ne_of_gt hWt1) (ne_of_gt hWt)]
  have hratio := potential_ratio_le η hη ℓ hℓ t ht
  set c := (1 : ℝ) - Real.exp (-η)
  -- The ratio is positive (from hratio and the fact W_{t+1}/W_t > 0)
  have hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
    div_pos hWt1 hWt
  have h1mc_pos : 0 < 1 - c * hedgeLoss η ℓ t := by linarith
  -- log(ratio) ≤ log(1 - c * hedgeLoss) ≤ (1 - c * hedgeLoss) - 1 = -c * hedgeLoss
  -- using log x ≤ x - 1 for x > 0.
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log (1 - c * hedgeLoss η ℓ t) := by
        exact Real.log_le_log hratio_pos hratio
    _ ≤ (1 - c * hedgeLoss η ℓ t) - 1 := Real.log_le_sub_one_of_pos h1mc_pos
    _ = -(1 - Real.exp (-η)) * hedgeLoss η ℓ t := by ring
