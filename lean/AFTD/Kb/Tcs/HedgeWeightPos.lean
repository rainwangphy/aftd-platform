import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeWeight

/-!
# hedgeWeight_pos

Topic: learning   Node: 82104b880204

Provenance: helper lemma. TCSlib, `hedgeWeight_pos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of Hedge weights. Fix a learning rate $\eta \in \bbr$, a loss sequence $\ell$ for $N$ experts over $T$
rounds, a time $t$, and an expert $i$. Then the unnormalized Hedge weight $w_t(i) =
\exp\!\bigl(-\eta \cdot L_t(i)\bigr)$, where $L_t(i) = \sum_{s < t} \ell_s(i)$ is the
cumulative loss of expert $i$ through the first $t$ rounds, is strictly positive.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Every Hedge weight is strictly positive, being an exponential. -/
lemma hedgeWeight_pos {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 < hedgeWeight η ℓ t i := by
  exact exp_pos _
