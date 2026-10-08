import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq

/-!
# cumLoss

Topic: learning   Node: b57db36a6eb2

Provenance: formalization of a published result. Source: TCSlib, `cumLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{cumulative loss} of expert $i$ through the first $t$ rounds is
\[
  L_t(i) \;=\; \sum_{s < t} \ell_s(i),
\]
where the sum ranges over all rounds $s \in \mathrm{Fin}\,T$ with $s < t$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The cumulative loss `L_t(i) = ∑_{s < t} ℓ_s(i)` of expert `i` through the first `t` rounds [FS97, §2]; [CBL06, §2.1]. This sums exactly the rounds whose index is less than `t`. -/
noncomputable def cumLoss {N T : ℕ} (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  ((Finset.univ (α := Fin T)).filter (fun s => s.val < t)).sum (fun s => ℓ s i)
