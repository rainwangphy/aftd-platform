import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.Tcs.HedgeDistNonneg
import AFTD.Kb.Tcs.HedgeDistSum
import AFTD.Kb.Tcs.HedgeLoss

/-!
# hedgeLoss_le_one

Topic: learning   Node: 93d75ed151b1

Provenance: helper lemma. TCSlib, `hedgeLoss_le_one`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Hedge's expected loss is at most one. Fix a learning rate $\eta \in \bbr$, and let $\ell$ be a valid loss sequence for $N \ge
1$ experts over $T$ rounds, so that $0 \le \ell_t(i) \le 1$ for every round $t$ and
expert $i$. Then at each round $t$ the expected loss of the learner under the Hedge
distribution satisfies $\widehat{\ell}_t \le 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For a valid loss sequence, Hedge's expected loss at each round is at most `1`. -/
lemma hedgeLoss_le_one {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : hedgeLoss η ℓ t ≤ 1 := by
  -- A convex combination of losses in `[0, 1]` is at most `1`.
  have hsum : hedgeLoss η ℓ t ≤ ∑ i : Fin N, hedgeDist η ℓ t.val i * 1 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hℓ t i).2 (hedgeDist_nonneg η ℓ t.val i)
  simp only [mul_one] at hsum
  linarith [hedgeDist_sum η ℓ t.val]
