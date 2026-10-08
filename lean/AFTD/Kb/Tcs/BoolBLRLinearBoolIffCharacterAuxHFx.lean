import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHFx2
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# BoolBLR.linear_bool_iff_character_aux_h_fx

Topic: interactive   Node: 78c9d1ea7f7c

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_fx`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Value of a linear Boolean function from its action on basis vectors. Let $f : \{0,1\}^n \to \{0,1\}$ be a linear Boolean function, meaning $f(x \oplus y) =
f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$, where $\oplus$ is componentwise XOR. For
each coordinate $i$, let $e_i \in \{0,1\}^n$ denote the standard basis vector that is
$1$ in coordinate $i$ and $0$ elsewhere. Then for every $x \in \{0,1\}^n$, the value
$f(x)$ is $1$ if the number of coordinates $i$ with $x_i = 1$ and $f(e_i) = 1$ is odd,
and $0$ if that number is even; equivalently, $f(x)$ is the parity of $\lvert\{\, i :
x_i = 1 \text{ and } f(e_i) = 1 \,\}\rvert$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_fx {n : ℕ} (f : hypercube n → Bool) (hf : is_linear_bool f) (x : BooleanAnalysis.BoolCube n) :
    f x =
  if (∑ i with x i = true, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false
  else true :=
  (linear_bool_iff_character_aux_h_fx_2 f hf x)
