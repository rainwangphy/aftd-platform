import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.Regret
import AFTD.Kb.Tcs.LogPotentialStepTight
import AFTD.Kb.Tcs.RegretLeOfLogPotentialStep
import AFTD.Kb.Tcs.Rate

/-!
# hedge_regret_bound_tight

Topic: learning   Node: 2b14bd7d2395

Provenance: helper lemma. TCSlib, `hedge_regret_bound_tight`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tight Hedge regret bound. Fix $N \ge 1$ experts and a horizon of $T$ rounds, and run the Hedge algorithm with a
learning rate $\eta > 0$. For every valid loss sequence $\ell$ — one whose losses
satisfy $0 \le \ell_t(i) \le 1$ for all rounds $t$ and experts $i$ — the regret of Hedge
is bounded by
\[
  R_T(\eta) \;\le\; \frac{\log N}{\eta} + \frac{\eta\,T}{8}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- **Hedge regret bound** (tight constant): for any valid loss sequence with `N` experts, `T` rounds, and any learning rate `η > 0`, the regret of Hedge is at most `(ln N)/η + ηT/8` [CBL06, Thm 2.2]; [MRT18, §8.2.4]. Deviation: stated in the expert-loss (linear) setting rather than for a convex loss of a weighted-average prediction; the constant and the hypotheses otherwise match CBL exactly (the prediction-space form is `hedgePrediction_regret_bound_tight` in `Hedge.ConvexPrediction`). This is the theorem reused by the adaptive-episode layer: once an online interaction has generated a valid `LossSeq`, the bound applies directly. **Proof sketch.** The theorem instantiates the shared potential argument `regret_le_of_log_potential_step` with `c = η²/8`. Step 1: for each round, `log_potential_step_tight` (Hoeffding's lemma) gives `log W_{t+1} - log W_t ≤ -η · hedgeLoss_t + η²/8`; no `η ≤ 1` is needed. Step 2: apply `regret_le_of_log_potential_step`. Step 3: simplify the constant `(η²/8) · T / η = ηT/8`. -/
theorem hedge_regret_bound_tight {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 8 := by
  -- Step 1: tight per-step bound from Hoeffding's lemma (no `η ≤ 1` needed)
  have hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 8 :=
    fun t => log_potential_step_tight η hη_pos ℓ hℓ t (by omega)
  -- Step 2: shared potential argument with c = η²/8
  -- Step 3: constant algebra (η²/8)·T/η = ηT/8
  calc regret η ℓ ≤ Real.log N / η + η ^ 2 / 8 * T / η :=
        regret_le_of_log_potential_step η hη_pos ℓ (η ^ 2 / 8) hstep
    _ = Real.log N / η + η * T / 8 := by
        congr 1
        rw [div_eq_iff (ne_of_gt hη_pos)]
        ring
