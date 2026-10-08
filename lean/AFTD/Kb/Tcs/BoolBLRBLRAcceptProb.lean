import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.BLR_accept_prob

Topic: interactive   Node: 41ea7ddd0cb7

Provenance: formalization of a published result. Source: TCSlib, `BoolBLR.BLR_accept_prob`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{BLR acceptance probability} of $f : \{0,1\}^n \to \{0,1\}$ is
\[
  \Pr_{x,y}[\text{BLR accepts}]
  \;=\;
  \E_{x}\!\left[\E_{y}\!\left[
    \mathbf{1}\!\left[
      \texttt{BoolBLR.lift\_pm1}\,f(x \oplus y)
      = \texttt{BoolBLR.lift\_pm1}\,f(x)\cdot\texttt{BoolBLR.lift\_pm1}\,f(y)
    \right]
  \right]\right],
\]
where $x, y$ are drawn uniformly from $\{0,1\}^n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Defines the acceptance probability of the Boolean BLR linearity test. **Source:** [OD14, §1.6]. -/
noncomputable def BoolBLR.BLR_accept_prob {n : ℕ} (f : hypercube n → Bool) : ℝ :=
  expectation (fun x =>
    expectation (fun y =>
      if lift_pm1 f (xor_vec x y) = lift_pm1 f x * lift_pm1 f y then 1 else 0))

-- Pr [ BLR accepts f ] = ( 1 + E [ E [ f(x) f(y) f(x + y) ] ] ) / 2
