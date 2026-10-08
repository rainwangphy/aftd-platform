import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierHypercube

/-!
# BoolBLR.bool_dist

Topic: interactive   Node: bfd5be05dc06

Provenance: formalization of a published result. Source: TCSlib, `BoolBLR.bool_dist`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{distance} between two Boolean functions
$f, g : \{0,1\}^n \to \{0,1\}$ is
\[
  \dist(f, g) \;=\; \Pr_{x \sim \{0,1\}^n}[f(x) \ne g(x)],
\]
computed as the uniform expectation of the indicator $\mathbf{1}[f(x) \ne g(x)]$.
-/

open Finset BoolFourier in
/-- Defines the uniform Hamming distance between two Boolean functions. **Source:** [OD14, §1.6]. -/
noncomputable def BoolBLR.bool_dist {n : ℕ}
    (f g : hypercube n → Bool) : ℝ :=
  expectation (fun x =>
    if f x = g x then 0 else 1)
