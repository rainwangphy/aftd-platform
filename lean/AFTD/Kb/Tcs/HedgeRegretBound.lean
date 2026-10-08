import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.HedgeLossLeOne
import AFTD.Kb.Tcs.HedgeLossNonneg
import AFTD.Kb.Tcs.LogPotentialStep
import AFTD.Kb.Tcs.OneSubExpNegGe
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.Regret
import AFTD.Kb.Tcs.RegretLeOfLogPotentialStep
import AFTD.Kb.Tcs.Rate

/-!
# hedge_regret_bound

Topic: learning   Node: fc81af37bd0c

Provenance: formalization of a published result. Source: Regret bound for the Hedge algorithm, as formalized in TCSlib (`hedge_regret_bound`). Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Regret bound for the Hedge algorithm. Fix $N \ge 1$ experts and $T$ rounds, and let $\ell$ be a valid loss sequence, so that
$0 \le \ell_t(i) \le 1$ for every round $t$ and expert $i$. Then for any learning rate
$\eta$ with $0 < \eta \le 1$, the regret of the Hedge algorithm satisfies
\[
  R_T(\eta) \;\le\; \frac{\ln N}{\eta} + \frac{\eta\,T}{2}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- **Hedge regret bound** (weak constant): for any valid loss sequence with `N` experts, `T` rounds, and learning rate `η ∈ (0,1]`, the regret of Hedge is at most `(ln N)/η + ηT/2` [CBL06, Thm 2.2]; [FS97, §2.1, Thm 2 / Eq. (9) (with `β = e^{-η}`)]. Deviation: the constant is `ηT/2` because the per-step bound uses the elementary chord inequality `e^{-ηx} ≤ 1 - (1 - e^{-η})x` and the relaxation `1 - e^{-η} ≥ η - η²/2` instead of Hoeffding's lemma. The hypothesis `η ≤ 1` is carried over from the original formalization; the argument does not depend on it (the relaxation holds for all `η > 0`), so the bound is weaker than CBL's only in the constant `ηT/2` vs `ηT/8`. CBL's constant `ηT/8` for every `η > 0` is `hedge_regret_bound_tight`. **Proof sketch.** The theorem instantiates the shared potential argument `regret_le_of_log_potential_step` with `c = η²/2`. Step 1: for each round, `log_potential_step` gives `log W_{t+1} - log W_t ≤ -(1 - e^{-η}) · hedgeLoss_t`; relax with `1 - e^{-η} ≥ η - η²/2` (`one_sub_exp_neg_ge`) and `hedgeLoss_t ∈ [0,1]` to get `≤ -η · hedgeLoss_t + η²/2`. Step 2: apply `regret_le_of_log_potential_step`. Step 3: simplify the constant `(η²/2) · T / η = ηT/2`. -/
theorem hedge_regret_bound {N T : ℕ} [NeZero N] (η : ℝ)
    (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) :
    regret η ℓ ≤ Real.log N / η + η * T / 2 := by
  -- Step 1: per-step bound `log_potential_step`, relaxed via `1 - exp(-η) ≥ η - η²/2`
  have hrelax : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + η ^ 2 / 2 := by
    intro t
    have h1 := log_potential_step η hη_pos ℓ hℓ t (by omega)
    have hge := @one_sub_exp_neg_ge η hη_pos
    have hle1 := hedgeLoss_le_one η ℓ hℓ t
    have hnn := hedgeLoss_nonneg η ℓ hℓ t
    nlinarith [sq_nonneg η]
  -- Step 2: shared potential argument with c = η²/2
  -- Step 3: constant algebra (η²/2)·T/η = ηT/2
  calc regret η ℓ ≤ Real.log N / η + η ^ 2 / 2 * T / η :=
        regret_le_of_log_potential_step η hη_pos ℓ (η ^ 2 / 2) hrelax
    _ = Real.log N / η + η * T / 2 := by
        congr 1
        rw [div_eq_iff (ne_of_gt hη_pos)]
        ring
