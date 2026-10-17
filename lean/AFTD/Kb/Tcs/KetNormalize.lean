import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetApply
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra

/-!
# Ket.normalize

Topic: quantum   Node: 22bdc8cb7f42

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.normalize`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Create a ket out of a vector given it has a nonzero component
-/

set_option quotPrecheck false
open Braket
local notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open BigOperators in
open ComplexConjugate in
open Kronecker in
open scoped Matrix ComplexOrder in
variable {d : Type*} [Fintype d] in
/-- Create a ket out of a vector given it has a nonzero component -/
noncomputable def Ket.normalize (v : d → ℂ) (h : ∃ x, v x ≠ 0) : Ket d :=
  { vec := fun x ↦ v x / √(∑ x : d, ‖v x‖ ^ 2),
    normalized' := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_div,
        Complex.normSq_ofReal, ←sq]
      have hnonneg : ∑ x : d, Complex.normSq (v x) ≥ 0 := Fintype.sum_nonneg (fun x => Complex.normSq_nonneg (v x))
      simp only [Real.sq_sqrt hnonneg, div_eq_inv_mul, ←Finset.mul_sum]
      apply inv_mul_cancel₀
      by_contra hzero
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (v x))] at hzero
      obtain ⟨a, ha⟩ := h
      have h₁ : (fun x => Complex.normSq (v x)) a ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact ha
      exact h₁ (congrFun hzero a)
  }
