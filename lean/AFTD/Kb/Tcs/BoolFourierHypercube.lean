import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolFourier.hypercube

Topic: interactive   Node: 80e2601962b4

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.hypercube`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Boolean hypercube of dimension $n$ is the type $\{0,1\}^n$, defined as an
abbreviation for \texttt{BooleanAnalysis.BoolCube} $n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Names the `n`-dimensional Boolean hypercube. **Source:** [OD14, §1.3]. -/
abbrev BoolFourier.hypercube (n : ℕ) := BoolCube n
