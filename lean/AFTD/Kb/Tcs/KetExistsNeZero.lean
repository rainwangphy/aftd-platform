import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.KetNormalized
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra

/-!
# Ket.exists_ne_zero

Topic: quantum   Node: c1eaf0aef2d5

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.exists_ne_zero`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ket.exists_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
open Braket in
variable {d : Type*} [Fintype d] in
theorem Ket.exists_ne_zero (ψ : Ket d) : ∃ x, ψ x ≠ 0 := by
  have hzerolt : ∑ x : d, Complex.normSq (ψ x) > ∑ x : d, 0 := by rw [ψ.normalized, Finset.sum_const_zero]; exact zero_lt_one
  have hpos : ∃ x ∈ Finset.univ, 0 < Complex.normSq (ψ x) := Finset.exists_lt_of_sum_lt hzerolt
  obtain ⟨x, _, hpos⟩ := hpos
  rw [Complex.normSq_pos] at hpos
  use x
