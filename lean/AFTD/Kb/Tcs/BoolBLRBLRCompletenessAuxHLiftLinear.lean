import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierBoolToPM1Xor
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.BLR_completeness_aux_h_lift_linear

Topic: interactive   Node: 3abe33f0768d

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_completeness_aux_h_lift_linear`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Multiplicativity of the sign lift of an XOR-homomorphism. Let $f : \{0,1\}^n \to \{0,1\}$ be a function that respects componentwise XOR, meaning
$f(x \oplus y) = f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$, and let $g : \{0,1\}^n
\to \bbr$ be its $\pm 1$ lift, $g(x) = (-1)^{f(x)}$. Then $g$ turns XOR into
multiplication:
\[
  g(x \oplus y) \;=\; g(x)\,g(y) \qquad \text{for all } x, y \in \{0,1\}^n.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.BLR_completeness_aux_h_lift_linear {n : ℕ} (f : BoolFourier.hypercube n → Bool) (h_linear : ∀ (x y : BoolFourier.hypercube n), f (BoolFourier.xor_vec x y) = (f x ^^ f y)) :
    ∀ (x y : BoolFourier.hypercube n), lift_pm1 f (BoolFourier.xor_vec x y) = lift_pm1 f x * lift_pm1 f y :=
  by
  intros x y; exact (by
  convert BoolToPM1_xor ( f x ) ( f y ) using 1 <;> try rfl
  exact h_linear x y ▸ rfl);
