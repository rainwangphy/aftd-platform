import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolFourier.card_hypercube

Topic: interactive   Node: 065864d9633f

Provenance: helper lemma. TCSlib, `BoolFourier.card_hypercube`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cardinality of the Boolean hypercube. For every natural number $n$, the Boolean hypercube $\{0,1\}^n$ has exactly $2^n$
elements.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Computes the cardinality of the `n`-dimensional Boolean cube. **Source:** [OD14, §1.3]. -/
lemma BoolFourier.card_hypercube (n : ℕ) : Fintype.card (hypercube n) = 2 ^ n := by
  simp [hypercube, BoolCube, Fintype.card_pi]
