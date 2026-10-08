import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.BestExpertLoss
import AFTD.Kb.Tcs.HedgeCumLoss

/-!
# regret

Topic: learning   Node: a7afc82ac69a

Provenance: formalization of a published result. Source: TCSlib, `regret`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{regret} of the Hedge algorithm is the excess cumulative loss over the
best expert in hindsight:
\[
  R_T(\eta) \;=\; \widehat{L}_T - L^*.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The regret of Hedge: its cumulative expected loss minus the cumulative loss of the best expert in hindsight [CBL06, §2.1]; [FS97, §2]. -/
noncomputable def regret {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) : ℝ :=
  hedgeCumLoss η ℓ - bestExpertLoss ℓ
