import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BoolFourier.BoolFun

Topic: interactive   Node: dc238ea3752d

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.BoolFun`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Boolean function of arity $n$ is an element of type $\{0,1\}^n \to \mathbb{R}$,
defined as an abbreviation for \texttt{BooleanAnalysis.BooleanFunc} $n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Names real-valued functions on the `n`-dimensional Boolean hypercube. **Source:** [OD14, §1.3]. -/
abbrev BoolFourier.BoolFun (n : ℕ) := BooleanFunc n
