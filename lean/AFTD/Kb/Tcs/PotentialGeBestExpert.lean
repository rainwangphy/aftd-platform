import AFTD.Prelude
import AFTD.Kb.Tcs.CumLoss
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.BestExpertLoss
import AFTD.Kb.Tcs.LossSeq

/-!
# potential_ge_best_expert

Topic: learning   Node: fb47ec85a907

Provenance: helper lemma. TCSlib, `potential_ge_best_expert`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Potential lower bound via the best expert. Fix $N \ge 1$ experts and $T$ rounds, a loss sequence $\ell$, and a learning rate $\eta
> 0$. Then the final potential is at least the unnormalized Hedge weight of the best
expert in hindsight:
\[
  W_T \;\ge\; \exp\!\bigl(-\eta \, L^*\bigr),
\]
where $L^* = \min_{i} L_T(i)$ is the smallest cumulative loss over the full horizon $T$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Lower bound on the final potential by the best expert: `W_T ≥ exp(-η · min_i L_T(i))`, since the sum of the final weights is at least the single largest weight [CBL06, proof of Thm 2.2]; [FS97, §2.1, proof of Thm 2]. The hypothesis `hη` is not used. -/
lemma potential_ge_best_expert {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) :
    potential η ℓ T ≥ Real.exp (-η * bestExpertLoss ℓ) := by
  -- The sum of all final weights is at least the single final weight of the
  -- best expert.  This is the lower-bound half of the potential method.
  simp only [bestExpertLoss, potential, ge_iff_le, hedgeWeight]
  -- ⨅ is achieved at some i₀ (Fin N is finite nonempty).
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min (cumLoss ℓ T)
  -- hi₀ : ∀ j, cumLoss ℓ T i₀ ≤ cumLoss ℓ T j
  -- So cumLoss i₀ = ⨅ cumLoss.
  have hinf : ⨅ i, cumLoss ℓ T i = cumLoss ℓ T i₀ :=
    le_antisymm (ciInf_le ⟨_, by rintro _ ⟨j, rfl⟩; exact hi₀ j⟩ i₀) (le_ciInf hi₀)
  rw [hinf]
  -- Goal: exp(-η * cumLoss i₀) ≤ ∑ exp(-η * cumLoss i)
  exact Finset.single_le_sum (f := fun i => Real.exp (-η * cumLoss ℓ T i))
    (fun i _ => (exp_pos _).le) (Finset.mem_univ i₀)
