import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.Tcs.HedgeDistNonneg
import AFTD.Kb.Tcs.HedgeLoss

/-!
# hedgeLoss_nonneg

Topic: learning   Node: 9d1673cb2843

Provenance: helper lemma. TCSlib, `hedgeLoss_nonneg`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of Hedge's expected loss. Let $\ell$ be a valid loss sequence for $N \ge 1$ experts over $T$ rounds, fix any
learning rate $\eta \in \bbr$, and let $t$ be one of the rounds. Then the learner's
expected loss $\widehat{\ell}_t = \sum_{i=1}^{N} p_t(i)\,\ell_t(i)$ under the Hedge
distribution is nonnegative, $\widehat{\ell}_t \ge 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For a valid loss sequence, Hedge's expected loss at each round is nonnegative. -/
lemma hedgeLoss_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (hℓ : ℓ.Valid)
    (t : Fin T) : 0 ≤ hedgeLoss η ℓ t := by
  -- A convex combination of nonnegative losses is nonnegative.
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hedgeDist_nonneg η ℓ t.val i) (hℓ t i).1
