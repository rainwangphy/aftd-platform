import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolToPM1Xor
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BoolBLR.linear_bool_iff_character_aux_h_char

Topic: interactive   Node: bfdf365c0faa

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_char`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multiplicativity of the Walsh characters. Fix $n$ and a subset $S \subseteq [n]$, and let $\chi_S(x) = \prod_{i \in S}(-1)^{x_i}$
be the associated Walsh character on the hypercube $\{0,1\}^n$. Then for all $x, y \in
\{0,1\}^n$,
\[
  \chi_S(x \oplus y) \;=\; \chi_S(x)\,\chi_S(y),
\]
where $x \oplus y$ denotes the componentwise XOR.
-/

open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_char {n : ℕ} (S : Finset (Fin n)) (x : BoolFourier.hypercube n) (y : BoolFourier.hypercube n) :
    BoolFourier.char_S S (BoolFourier.xor_vec x y) = BoolFourier.char_S S x * BoolFourier.char_S S y :=
  by
  simp only [char_S, BooleanAnalysis.chiS, ← Finset.prod_mul_distrib]
  congr 1 ; ext i ; simp [xor_vec, BoolToPM1_xor]
