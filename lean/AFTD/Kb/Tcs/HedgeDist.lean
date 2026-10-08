import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeWeight
import AFTD.Kb.Tcs.Potential

/-!
# hedgeDist

Topic: learning   Node: 55481887b312

Provenance: formalization of a published result. Source: TCSlib, `hedgeDist`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{Hedge distribution} at round $t$ is the normalization of the weight
vector:
\[
  p_t(i) \;=\; \frac{w_t(i)}{W_t}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The Hedge distribution at round `t`: the normalized weights `p_t(i) = w_t(i) / W_t` [FS97, §2]; [CBL06, §2.1]. -/
noncomputable def hedgeDist {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  hedgeWeight η ℓ t i / potential η ℓ t
