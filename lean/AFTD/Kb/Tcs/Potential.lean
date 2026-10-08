import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeWeight

/-!
# potential

Topic: learning   Node: ba960a0be3ed

Provenance: formalization of a published result. Source: TCSlib, `potential`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{potential} (sum of unnormalized weights) at time $t$ is
\[
  W_t \;=\; \sum_{i=1}^{N} w_t(i).
\]
The potential telescopes to relate the learner's cumulative loss to the best
expert's loss.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The potential `W_t = ∑_i w_t(i)`, the sum of the unnormalized weights at round `t` [FS97, §2]; [CBL06, proof of Thm 2.2]. The potential is the object we track: its one-step upper bound gives Hedge's cumulative loss, while its final lower bound sees the best expert. -/
noncomputable def potential {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : ℝ :=
  ∑ i : Fin N, hedgeWeight η ℓ t i
