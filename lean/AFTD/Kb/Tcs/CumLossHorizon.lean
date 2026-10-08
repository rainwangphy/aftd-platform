import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLoss

/-!
# cumLoss_horizon

Topic: learning   Node: 42c4be10cd28

Provenance: helper lemma. TCSlib, `cumLoss_horizon`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cumulative loss at the horizon. Fix $N$ experts and a horizon $T$, and let $\ell$ be a loss sequence assigning to each
round $t$ and expert $i$ a real loss $\ell_t(i)$. For every expert $i$, the cumulative
loss through the first $T$ rounds equals the total loss over all rounds: $L_T(i) =
\sum_{t} \ell_t(i)$, where $t$ ranges over all $T$ rounds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- At the final horizon `T`, the cumulative loss of expert `i` is the sum of its losses over all `T` rounds. -/
lemma cumLoss_horizon {N T : ℕ} (ℓ : LossSeq N T) (i : Fin N) :
    cumLoss ℓ T i = ∑ t : Fin T, ℓ t i := by
  simp only [cumLoss]
  congr 1
  ext t
  simp
