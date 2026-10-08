import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BoolFourier.char_S

Topic: interactive   Node: 2736fa38cfee

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.char_S`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a set $S \subseteq [n]$, the Walsh character
$\chi_S : \{0,1\}^n \to \mathbb{R}$ is
\[
  \chi_S(x) = \prod_{i \in S} (-1)^{x_i},
\]
defined as an alias for \texttt{BooleanAnalysis.chiS}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Names the Fourier--Walsh character indexed by a subset of coordinates. **Source:** [OD14, §1.3]. -/
noncomputable abbrev BoolFourier.char_S {n : ℕ} (S : Finset (Fin n)) : BoolFun n := chiS S
