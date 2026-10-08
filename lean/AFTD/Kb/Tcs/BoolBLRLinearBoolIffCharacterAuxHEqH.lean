import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHChar
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHEq
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.linear_bool_iff_character_aux_h_eq_h

Topic: interactive   Node: cdf96128ea46

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_eq_h`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

XOR-additivity of a Boolean function that lifts to a character. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function whose $\pm 1$ lift $x
\mapsto (-1)^{f(x)}$ coincides with the Walsh character $\chi_S$ for some subset $S
\subseteq [n]$. Then for all $x, y \in \{0,1\}^n$,
\[
  (-1)^{f(x \oplus y)} \;=\; (-1)^{f(x) \oplus f(y)},
\]
where $x \oplus y$ denotes the componentwise XOR of $x$ and $y$ and $f(x) \oplus f(y)$
the XOR of the two Boolean outputs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_eq_h {n : ℕ} (f : hypercube n → Bool) (S : Finset (Fin n)) (hS : lift_pm1 f = char_S S) (x : hypercube n) (y : hypercube n) :
    BoolToPM1 (f (xor_vec x y)) = BoolToPM1 (f x ^^ f y) :=
  (linear_bool_iff_character_aux_h_eq f S hS x y (linear_bool_iff_character_aux_h_char S x y))
