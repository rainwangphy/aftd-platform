import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolFourierBoolToPM1Xor
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.linear_bool_iff_character_aux_h_eq

Topic: interactive   Node: eb8644c9ea34

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_eq`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

XOR-additivity of a Boolean function whose lift is a character. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function whose $\pm 1$ lift
coincides with a Walsh character, say $x \mapsto (-1)^{f(x)}$ equals $\chi_S$ for some
$S \subseteq [n]$, and fix points $x, y \in \{0,1\}^n$. If the character is
multiplicative at this pair, meaning $\chi_S(x \oplus y) = \chi_S(x)\,\chi_S(y)$ where
$x \oplus y$ denotes the componentwise XOR, then
\[
  (-1)^{f(x \oplus y)} \;=\; (-1)^{f(x) \oplus f(y)}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_eq {n : ℕ} (f : BoolFourier.hypercube n → Bool) (S : Finset (Fin n)) (hS : lift_pm1 f = BoolFourier.char_S S) (x : BoolFourier.hypercube n) (y : BoolFourier.hypercube n) (h_char : BoolFourier.char_S S (BoolFourier.xor_vec x y) = BoolFourier.char_S S x * BoolFourier.char_S S y) :
    BoolFourier.BoolToPM1 (f (BoolFourier.xor_vec x y)) = BoolFourier.BoolToPM1 (f x ^^ f y) :=
  by
  unfold lift_pm1 at hS;
  rw [congr_fun hS (xor_vec x y), h_char, ← congr_fun hS x, ← congr_fun hS y, ← BoolToPM1_xor]
