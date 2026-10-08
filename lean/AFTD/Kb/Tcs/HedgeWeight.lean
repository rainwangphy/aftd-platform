import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLoss

/-!
# hedgeWeight

Topic: learning   Node: 453ef5434ee4

Provenance: formalization of a published result. Source: TCSlib, `hedgeWeight`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{unnormalized Hedge weight} of expert $i$ at time $t$ with learning
rate $\eta$ is
\[
  w_t(i) \;=\; \exp\!\bigl(-\eta \cdot L_t(i)\bigr).
\]
Experts with smaller cumulative loss receive larger weight.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The unnormalized Hedge weight `w_t(i) = exp(-η · L_t(i))` of expert `i` at round `t` [FS97, §2 (Hedge(β) with `β = e^{-η}`)]; [CBL06, §2.1]. Experts with smaller cumulative loss get larger exponential weight. -/
noncomputable def hedgeWeight {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  Real.exp (-η * cumLoss ℓ t i)
