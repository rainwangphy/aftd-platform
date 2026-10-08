import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.ExpNegLeLinear
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.Tcs.HedgeLoss
import AFTD.Kb.Tcs.HedgeWeight
import AFTD.Kb.Tcs.HedgeWeightPos
import AFTD.Kb.Tcs.HedgeWeightSucc
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.Tcs.PotentialPos

/-!
# potential_ratio_le

Topic: learning   Node: 56d2ecf32572

Provenance: helper lemma. TCSlib, `potential_ratio_le`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Potential ratio bound for Hedge. Fix $N \ge 1$ experts, a horizon of $T$ rounds, a learning rate $\eta > 0$, and a valid
loss sequence $\ell$. Then for every round $t$ with $t < T$, the consecutive potentials
satisfy
\[
  \frac{W_{t+1}}{W_t} \;\le\; 1 - \bigl(1 - e^{-\eta}\bigr)\,\widehat{\ell}_t,
\]
where $\widehat{\ell}_t = \sum_{i=1}^{N} p_t(i)\,\ell_t(i)$ is the expected loss of the
learner under the Hedge distribution at round $t$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- One-step potential ratio bound: for a valid loss sequence and `η > 0`, `W_{t+1} / W_t ≤ 1 - (1 - exp(-η)) · (p_t · ℓ_t)`, where `p_t · ℓ_t` is Hedge's expected loss at round `t` [CBL06, proof of Thm 2.2]; [FS97, §2.1, Eq. (4) (proof of Lemma 1)]. Deviation: each term is bounded with the elementary chord inequality `exp_neg_le_linear` instead of Hoeffding's lemma, which is why the downstream weak bound has `ηT/2` rather than `ηT/8`. (An earlier docstring called this "CBL Lemma 2.2"; that lemma is Hoeffding's lemma, used only in the tight bound.) The hypothesis `ht` is not used. **Proof sketch.** Multiply through by `W_t > 0`. Step 1: by the multiplicative weight update, `W_{t+1} = ∑_i w_t(i) exp(-η ℓ_t(i))`. Step 2: bound each summand by `w_t(i) (1 - (1 - e^{-η}) ℓ_t(i))` using `exp_neg_le_linear` on `ℓ_t(i) ∈ [0,1]`. Step 3: sum the bounds and identify `∑_i w_t(i) (1 - c ℓ_t(i)) = (1 - c · hedgeLoss) · W_t` with `c = 1 - e^{-η}`, using `hedgeLoss = (∑_i w_t(i) ℓ_t(i)) / W_t`. -/
lemma potential_ratio_le {N T : ℕ} [NeZero N] (η : ℝ) (hη : 0 < η)
    (ℓ : LossSeq N T) (hℓ : ℓ.Valid) (t : Fin T) (ht : t.val + 1 ≤ T) :
    potential η ℓ (t.val + 1) / potential η ℓ t.val
      ≤ 1 - (1 - Real.exp (-η)) * hedgeLoss η ℓ t := by
  -- This is the core one-step Hedge estimate.  The only use of validity is
  -- that every coordinate of the current loss vector lies in `[0, 1]`.
  -- W_{t+1} = ∑_i w_t(i) · exp(-η · ℓ_t(i))
  -- W_{t+1}/W_t = ∑_i p_t(i) · exp(-η · ℓ_t(i))
  --            ≤ ∑_i p_t(i) · (1 - (1-e^{-η}) · ℓ_t(i))    [by exp_neg_le_linear]
  --            = 1 - (1-e^{-η}) · ∑_i p_t(i) · ℓ_t(i)
  --            = 1 - (1-e^{-η}) · hedgeLoss
  have hWt := potential_pos η ℓ t.val
  -- Step 1: clear the denominator and rewrite `W_{t+1}` by the multiplicative weight update
  rw [div_le_iff₀ hWt]
  -- Goal: potential η ℓ (t+1) ≤ (1 - (1 - exp(-η)) * hedgeLoss η ℓ t) * potential η ℓ t
  -- W_{t+1} = ∑ w_t(i) * exp(-η * ℓ_t(i))
  have hW_succ : potential η ℓ (t.val + 1) =
      ∑ i : Fin N, hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
    simp only [potential]; congr 1; ext i; exact hedgeWeight_succ η ℓ t i
  rw [hW_succ]
  -- Step 2: bound each summand with `exp_neg_le_linear`
  have hbound : ∀ i : Fin N,
      hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) ≤
      hedgeWeight η ℓ t.val i * (1 - (1 - Real.exp (-η)) * ℓ t i) := by
    intro i
    exact mul_le_mul_of_nonneg_left (exp_neg_le_linear hη (hℓ t i).1 (hℓ t i).2)
      (hedgeWeight_pos η ℓ t.val i).le
  -- Step 3: sum the bounds and show RHS = (1 - c * hedgeLoss) * W
  -- where c = 1 - exp(-η) and W = potential.
  -- RHS expanded: W - c * W * hedgeLoss = W - c * ∑(w_i * ℓ_i / W) * W = W - c * ∑ w_i * ℓ_i
  -- LHS ≤ ∑ w_i * (1 - c * ℓ_i) = ∑ w_i - c * ∑ w_i * ℓ_i = W - c * ∑ w_i * ℓ_i = RHS ✓
  set c := (1 : ℝ) - Real.exp (-η) with hc_def
  set W := potential η ℓ t.val with hW_def
  -- Expand the RHS
  have hW_ne : W ≠ 0 := ne_of_gt hWt
  -- hedgeLoss = (∑ w_i * ℓ_i) / W
  have hHL : hedgeLoss η ℓ t = (∑ i : Fin N, hedgeWeight η ℓ t.val i * ℓ t i) / W := by
    simp only [hedgeLoss, hedgeDist, hW_def, Finset.sum_div]
    congr 1; ext i; ring
  -- Goal: ∑ w_i * exp(-η * ℓ_i) ≤ (1 - c * hedgeLoss) * W
  -- ≤ ∑ w_i * (1 - c * ℓ_i) (from hbound)
  -- = ∑ w_i - c * ∑ w_i * ℓ_i
  -- = W - c * hedgeLoss * W = (1 - c * hedgeLoss) * W ✓
  have step1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hbound i
  suffices ∑ i, hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) =
      (1 - c * hedgeLoss η ℓ t) * W by linarith
  rw [hHL, hW_def, potential]
  have hW_ne : (∑ i : Fin N, hedgeWeight η ℓ t.val i) ≠ 0 := ne_of_gt hWt
  have : ∀ i : Fin N, hedgeWeight η ℓ t.val i * (1 - c * ℓ t i) =
      hedgeWeight η ℓ t.val i - c * (hedgeWeight η ℓ t.val i * ℓ t i) := by
    intro i; ring
  simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp
