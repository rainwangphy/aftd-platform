import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.BLR_completeness_aux_h_linear

Topic: interactive   Node: add6e50e56ea

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_completeness_aux_h_linear`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linearity gives additivity on XOR. Let $f : \{0,1\}^n \to \{0,1\}$ be a linear function, meaning that $f(x \oplus y) = f(x)
\oplus f(y)$ for all $x, y \in \{0,1\}^n$, where $\oplus$ denotes componentwise XOR.
Then for all $x, y \in \{0,1\}^n$ we have $f(x \oplus y) = f(x) \oplus f(y)$.
-/

open Finset BoolFourier in
lemma BoolBLR.BLR_completeness_aux_h_linear {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hlin : is_linear_bool f) :
    ∀ (x y : BoolFourier.hypercube n), f (BoolFourier.xor_vec x y) = (f x ^^ f y) :=
  by
  exact hlin;
