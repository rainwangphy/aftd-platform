import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.is_linear_bool

Topic: interactive   Node: 151313c50fb3

Provenance: formalization of a published result. Source: TCSlib, `BoolBLR.is_linear_bool`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A function $f : \{0,1\}^n \to \{0,1\}$ is \emph{linear} if for all
$x, y \in \{0,1\}^n$ we have
\[
  f(x \oplus y) = f(x) \oplus f(y),
\]
where $\oplus$ denotes bitwise XOR (i.e.\ \texttt{Bool.xor}).
-/

open Finset BoolFourier in
/-- Defines a Boolean linear function by preservation of pointwise XOR. **Source:** [OD14, §1.6]. -/
def BoolBLR.is_linear_bool {n : ℕ} (f : hypercube n → Bool) : Prop :=
  ∀ x y, f (xor_vec x y) = Bool.xor (f x) (f y)
