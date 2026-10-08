import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolBLR.linear_bool_iff_character_aux_h_fx_1

Topic: interactive   Node: fe79c4c59251

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character_aux_h_fx_1`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Value of a linear Boolean function on an indicator vector. Let $f : \{0,1\}^n \to \{0,1\}$ be a linear Boolean function, meaning $f(x \oplus y) =
f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$, where $\oplus$ is componentwise XOR. For
a subset $s \subseteq \{0, \dots, n-1\}$, let $\mathbf{1}_s \in \{0,1\}^n$ be its
indicator vector, whose $i$-th coordinate is $1$ when $i \in s$ and $0$ otherwise, and
for each index $i$ let $e_i \in \{0,1\}^n$ be the standard basis vector, whose $i$-th
coordinate is $1$ and all others $0$. Then for every $s$ the value $f(\mathbf{1}_s)$ is
$0$ when
\[
  \sum_{i \in s} \mathbf{1}[\,f(e_i) = 1\,] \equiv 0 \pmod 2,
\]
and $1$ otherwise; that is, $f(\mathbf{1}_s)$ equals the parity of the number of $i \in
s$ with $f(e_i) = 1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.linear_bool_iff_character_aux_h_fx_1 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hf : is_linear_bool f) :
    ∀ (s : Finset (Fin n)),
  (f fun i => if i ∈ s then true else false) =
    if (∑ i ∈ s, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false else true :=
  by
  intro s;
  induction s using Finset.induction <;> simp_all +decide ;
  · -- Base case s = ∅: f(0,…,0) = false, computed using linearity at (0,0).
    convert (hf ( fun _ => false ) ( fun _ => false )) using 1;
    · rfl
    simp +decide;
  · -- Inductive step: peel off one element using the linearity hypothesis hf.
    rename_i i s hi hs; specialize hf ( fun j => decide ( j = i ) ) ( fun j => decide ( j ∈ s ) ) ; simp_all +decide [ Finset.filter_insert ] ;
    convert hf using 1;
    · congr! 2;
      by_cases hi : ‹Fin n› = i <;> by_cases hs : ‹Fin n› ∈ s <;> simp +decide [ hi, hs, xor_vec ];
      · assumption;
      · assumption;
    · grind +splitImp;
