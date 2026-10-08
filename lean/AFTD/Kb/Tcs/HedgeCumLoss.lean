import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeLoss

/-!
# hedgeCumLoss

Topic: learning   Node: 94ad7264415f

Provenance: formalization of a published result. Source: TCSlib, `hedgeCumLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{cumulative loss} of the Hedge algorithm over all $T$ rounds is
\[
  \widehat{L}_T \;=\; \sum_{t=0}^{T-1} \widehat{\ell}_t.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The cumulative expected loss `∑_{t < T} ∑_i p_t(i) ℓ_t(i)` of Hedge over the `T` rounds [FS97, §2]; [CBL06, §2.1]. -/
noncomputable def hedgeCumLoss {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  ∑ t : Fin T, hedgeLoss η ℓ t
