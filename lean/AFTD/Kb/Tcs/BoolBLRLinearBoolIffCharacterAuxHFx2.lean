import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHFx1
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# BoolBLR.linear_bool_iff_character_aux_h_fx_2

Topic: interactive   Node: 26a371afae46

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_fx_2`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Value of a linear Boolean function from its values on basis vectors. Let $f : \{0,1\}^n \to \{0,1\}$ be a linear Boolean function, meaning $f(x \oplus y) =
f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$, and for each coordinate $i$ let $e_i \in
\{0,1\}^n$ denote the standard basis vector that is $1$ in position $i$ and $0$
elsewhere. Then for every $x \in \{0,1\}^n$, the value $f(x)$ equals the parity of the
number of coordinates $i$ with $x_i = 1$ and $f(e_i) = 1$; that is, $f(x) = 1$ if that
count is odd and $f(x) = 0$ if it is even.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_fx_2 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hf : is_linear_bool f) (x : BooleanAnalysis.BoolCube n) :
    f x =
  if (∑ i with x i = true, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false
  else true :=
  by
  -- More general claim by induction on the support set s.

  -- Specialize to s = support of x.
  convert (linear_bool_iff_character_aux_h_fx_1 f hf) ( Finset.univ.filter fun i => x i = true ) using 2 ; aesop;
