import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierHypercube

/-!
# BoolFourier.xor_vec

Topic: interactive   Node: 4367cbb92e6d

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.xor_vec`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For $x, y \in \{0,1\}^n$, the vector $\mathrm{xor\_vec}(x,y)_i = x_i \oplus y_i$ is
the componentwise XOR, giving the group operation on $(\mathbb{F}_2)^n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines pointwise XOR, the group operation on the Boolean cube. **Source:** [OD14, §1.3]. -/
def BoolFourier.xor_vec {n : ℕ} (x y : hypercube n) : hypercube n :=
  fun i => Bool.xor (x i) (y i)
