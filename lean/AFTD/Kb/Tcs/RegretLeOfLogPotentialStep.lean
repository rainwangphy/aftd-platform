import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.BestExpertLoss
import AFTD.Kb.Tcs.HedgeCumLoss
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.PotentialGeBestExpert
import AFTD.Kb.Tcs.PotentialZero
import AFTD.Kb.Tcs.Regret
import AFTD.Kb.Tcs.LogPotentialTelescope

/-!
# regret_le_of_log_potential_step

Topic: learning   Node: c5953e7e808e

Provenance: helper lemma. TCSlib, `regret_le_of_log_potential_step`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Regret.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Regret from a per-step log-potential bound. Let $N \ge 1$, let $\eta > 0$, let $\ell$ be a loss sequence for $N$ experts over $T$
rounds, and let $c \in \bbr$.  Suppose that for every round $t < T$ the log potential
satisfies the one-step bound
\[
  \log W_{t+1} - \log W_t \;\le\; -\eta \cdot \mathrm{hedgeLoss}_t + c ,
\]
where $\mathrm{hedgeLoss}_t$ is the expected loss of Hedge in round $t$.  Then the
regret of Hedge is bounded by
\[
  \mathrm{regret}(\eta,\ell) \;\le\; \frac{\log N}{\eta} + \frac{c\,T}{\eta} .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Regret from a uniform per-step log-potential bound: if every round satisfies `log W_{t+1} - log W_t ≤ -η · hedgeLoss_t + c`, then `regret ≤ (log N)/η + cT/η`. This is the potential argument of [CBL06, proof of Thm 2.2] (also [FS97, §2.1, Lemma 1 and proof of Thm 2]) with the per-round constant abstracted; both `hedge_regret_bound` (`c = η²/2`) and `hedge_regret_bound_tight` (`c = η²/8`) are instances. **Proof sketch.** Step 1: sum the per-step bounds over the `T` rounds; the left side telescopes (`log_potential_telescope`) to `log W_T - log W_0`, and the right side is `-η · hedgeCumLoss + cT`. Step 2: `W_0 = N` (`potential_zero`), so `log W_0 = log N`. Step 3: `W_T ≥ exp(-η · bestExpertLoss)` (`potential_ge_best_expert`), so `log W_T ≥ -η · bestExpertLoss`. Step 4: combine into `-η · bestExpertLoss - log N ≤ -η · hedgeCumLoss + cT`, i.e. `η · regret ≤ log N + cT`, and divide by `η > 0`. -/
lemma regret_le_of_log_potential_step {N T : ℕ} [NeZero N] (η : ℝ) (hη_pos : 0 < η)
    (ℓ : LossSeq N T) (c : ℝ)
    (hstep : ∀ t : Fin T, Real.log (potential η ℓ (t.val + 1)) - Real.log (potential η ℓ t.val)
      ≤ -η * hedgeLoss η ℓ t + c) :
    regret η ℓ ≤ Real.log N / η + c * T / η := by
  -- Step 1: sum the per-step bounds and telescope
  have hsum : Real.log (potential η ℓ T) - Real.log (potential η ℓ 0)
      ≤ -η * hedgeCumLoss η ℓ + c * T := by
    have hbounds := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hstep t
    have hrhs : ∑ t : Fin T, (-η * hedgeLoss η ℓ t + c) = -η * hedgeCumLoss η ℓ + c * T := by
      simp only [hedgeCumLoss, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_fin]
      ring
    linarith [log_potential_telescope η ℓ]
  -- Step 2: W_0 = N
  have hW0 : Real.log (potential η ℓ 0) = Real.log N := by
    rw [potential_zero]
  -- Step 3: W_T ≥ exp(-η · bestExpertLoss)
  have hWT : Real.log (potential η ℓ T) ≥ -η * bestExpertLoss ℓ := by
    calc Real.log (potential η ℓ T) ≥ Real.log (Real.exp (-η * bestExpertLoss ℓ)) :=
          Real.log_le_log (exp_pos _) (potential_ge_best_expert η hη_pos ℓ)
      _ = -η * bestExpertLoss ℓ := Real.log_exp _
  -- Step 4: rearrange η · regret ≤ log N + cT
  unfold regret
  rw [← add_div, le_div_iff₀ hη_pos]
  nlinarith [hsum, hW0, hWT]
