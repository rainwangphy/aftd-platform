import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.Tcs.HedgeWeightPos
import AFTD.Kb.Tcs.PotentialPos

/-!
# hedgeDist_nonneg

Topic: learning   Node: c6e0f34b702a

Provenance: helper lemma. TCSlib, `hedgeDist_nonneg`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the Hedge distribution. Fix $N \ge 1$ experts and $T$ rounds, a learning rate $\eta \in \bbr$, and a loss
sequence $\ell$. For every time $t$ and every expert $i$, the Hedge distribution is
nonnegative, that is, $p_t(i) \ge 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Every coordinate of the Hedge distribution is nonnegative. -/
lemma hedgeDist_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 ≤ hedgeDist η ℓ t i :=
  div_nonneg (hedgeWeight_pos η ℓ t i).le (potential_pos η ℓ t).le
