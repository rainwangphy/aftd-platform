import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq

/-!
# LossSeq.Valid

Topic: learning   Node: 834176867468

Provenance: formalization of a published result. Source: TCSlib, `LossSeq.Valid`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A loss sequence $\ell$ is \emph{valid} if all individual losses are in $[0,1]$:
$\forall t\,i,\; 0 \le \ell_t(i) \le 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A loss sequence is valid if every loss `ℓ t i` lies in the interval `[0,1]` [CBL06, §2.1]. -/
def LossSeq.Valid {N T : ℕ} (ℓ : LossSeq N T) : Prop :=
  ∀ t i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1
