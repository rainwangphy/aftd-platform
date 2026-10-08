import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeWeightPos
import AFTD.Kb.Tcs.Potential

/-!
# potential_pos

Topic: learning   Node: 640f52723f75

Provenance: helper lemma. TCSlib, `potential_pos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the Hedge potential. Fix a learning rate $\eta \in \bbr$, a loss sequence $\ell$ for $N \ge 1$ experts over
$T$ rounds, and a time $t$. Then the potential at time $t$ is strictly positive:
\[
  W_t \;=\; \sum_{i=1}^{N} \exp\!\bigl(-\eta \cdot L_t(i)\bigr) \;>\; 0,
\]
where $L_t(i) = \sum_{s < t} \ell_s(i)$ is the cumulative loss of expert $i$ through the
first $t$ rounds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The potential is strictly positive: it is a nonempty sum of positive weights. -/
lemma potential_pos {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    0 < potential η ℓ t := by
  apply Finset.sum_pos
  · intro i _
    exact hedgeWeight_pos η ℓ t i
  · exact Finset.univ_nonempty
