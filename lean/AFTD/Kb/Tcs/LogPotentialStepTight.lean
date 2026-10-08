import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.HedgeLossLeOne
import AFTD.Kb.Tcs.HedgeLossNonneg
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.PotentialPos
import AFTD.Kb.Tcs.PotentialRatioLe
import AFTD.Kb.Tcs.HoeffdingLemma

/-!
# log_potential_step_tight

Topic: learning   Node: 46f4e3f057f2

Provenance: helper lemma. TCSlib, `log_potential_step_tight`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tight per-step logarithmic potential bound for Hedge. Fix $N \ge 1$ experts and a learning rate $\eta > 0$, and let $\ell$ be a valid loss
sequence over $T$ rounds, so that every individual loss satisfies $0 \le \ell_t(i) \le
1$. Write $W_t = \sum_{i=1}^{N} \exp(-\eta L_t(i))$ for the Hedge potential after $t$
rounds, and $\widehat{\ell}_t$ for the expected loss of the learner at round $t$ under
the Hedge distribution. Then for every round $t$ (with $0 \le t < T$),
\[
  \log W_{t+1} - \log W_t \;\le\; -\eta\,\widehat{\ell}_t + \frac{\eta^2}{8}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Tight one-step log-potential bound: for a valid loss sequence and `η > 0`, `ln W_{t+1} - ln W_t ≤ -η · hedgeLoss_t + η²/8` [CBL06, proof of Thm 2.2]. The hypothesis `ht` is only forwarded to `potential_ratio_le`, which does not use it. **Proof sketch.** Write `μ = hedgeLoss_t ∈ [0,1]`. Step 1: by `potential_ratio_le`, `W_{t+1}/W_t ≤ 1 - (1 - e^{-η}) μ = (1 - μ) + μ e^{-η}`. Step 2: take logarithms (the ratio is positive). Step 3: Hoeffding's lemma `hoeffding_lemma` with `p = μ`, `h = -η` bounds `ln((1 - μ) + μ e^{-η}) ≤ -ημ + η²/8`. -/
lemma log_potential_step_tight {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 := by
  -- Here `μ = hedgeLoss` lies in `[0,1]`.  The one-step potential ratio is
  -- bounded by `(1-μ) + μ exp(-η)`, and Hoeffding converts the logarithm of
  -- that expression into `-η μ + η^2/8`.
  have hWt := potential_pos η ℓ t.val
  have hWt1 := potential_pos η ℓ (t.val + 1)
  rw [← Real.log_div (ne_of_gt hWt1) (ne_of_gt hWt)]
  -- Step 1: W_{t+1}/W_t ≤ (1-μ) + μ·e^{-η} where μ = hedgeLoss
  have hratio := potential_ratio_le η hη ℓ hℓ t ht
  set μ := hedgeLoss η ℓ t
  have hμ0 := hedgeLoss_nonneg η ℓ hℓ t
  have hμ1 := hedgeLoss_le_one η ℓ hℓ t
  have hratio_pos : 0 < potential η ℓ (t.val + 1) / potential η ℓ t.val :=
    div_pos hWt1 hWt
  -- The ratio is ≤ (1-μ) + μ·e^{-η}
  have hcomp : 1 - (1 - Real.exp (-η)) * μ = (1 - μ) + μ * Real.exp (-η) := by ring
  -- Step 2: log monotonicity; Step 3: Hoeffding with p = μ, h = -η
  calc Real.log (potential η ℓ (t.val + 1) / potential η ℓ t.val)
      ≤ Real.log ((1 - μ) + μ * Real.exp (-η)) := by
        apply Real.log_le_log hratio_pos
        linarith [hcomp]
    _ ≤ μ * (-η) + (-η) ^ 2 / 8 :=
        hoeffding_lemma hμ0 hμ1
    _ = -η * μ + η ^ 2 / 8 := by ring
