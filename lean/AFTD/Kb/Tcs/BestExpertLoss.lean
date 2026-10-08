import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLoss

/-!
# bestExpertLoss

Topic: learning   Node: d87629cb8c29

Provenance: formalization of a published result. Source: TCSlib, `bestExpertLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{best expert loss in hindsight} is the minimum cumulative loss
achieved by any single expert:
\[
  L^* \;=\; \min_{i \in [N]} L_T(i) \;=\; \inf_{i : \mathrm{Fin}\,N} \,L_T(i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The cumulative loss `min_i L_T(i)` of the best expert in hindsight [FS97, §2]; [CBL06, §2.1]. This is an infimum over a finite nonempty set of experts, so later we can choose an expert attaining it when lower-bounding the final potential. -/
noncomputable def bestExpertLoss {N T : ℕ} (ℓ : LossSeq N T) : ℝ :=
  ⨅ i : Fin N, cumLoss ℓ T i
