import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeDist

/-!
# hedgeLoss

Topic: learning   Node: a4e63398663b

Provenance: formalization of a published result. Source: TCSlib, `hedgeLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{expected loss} of the learner at round $t$ under the Hedge
distribution is
\[
  \widehat{\ell}_t \;=\; \sum_{i=1}^{N} p_t(i)\,\ell_t(i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The expected loss `∑_i p_t(i) ℓ_t(i)` of the learner at round `t` under the Hedge distribution [FS97, §2]; [CBL06, §2.1]. Deviation: the loss is linear in the distribution (the expert setting of [FS97]), not CBL's convex loss of a weighted-average prediction; the latter is recovered in `Hedge.ConvexPrediction` via Jensen. -/
noncomputable def hedgeLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) : ℝ :=
  ∑ i : Fin N, hedgeDist η ℓ t.val i * ℓ t i
