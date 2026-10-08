import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolFourierHypercube

/-!
# BoolBLR.lift_pm1

Topic: interactive   Node: e5f2e3122656

Provenance: formalization of a published result. Source: TCSlib, `BoolBLR.lift_pm1`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given $f : \{0,1\}^n \to \{0,1\}$, its \emph{$\pm 1$ lift}
$\texttt{BoolBLR.lift\_pm1}\,f : \{0,1\}^n \to \mathbb{R}$ is defined by
$x \mapsto (-1)^{f(x)}$, converting each Boolean output to a real sign via
\texttt{BoolToPM1}.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Lifts a Boolean-valued function to its `{±1}`-valued encoding. **Source:** [OD14, §1.6]. -/
def BoolBLR.lift_pm1 (f : hypercube n → Bool) : BoolFun n :=
  fun x => BoolToPM1 (f x)
