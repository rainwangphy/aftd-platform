import AFTD.Prelude
import AFTD.Kb.Tcs.Ket
import AFTD.Kb.Tcs.KetIsProdProd
import AFTD.Kb.Tcs.KetNotIsEntangledProd
import AFTD.Kb.Tcs.BraketInstFunLikeKet
import AFTD.Kb.Tcs.InstBraOfKet
import AFTD.Kb.Tcs.InstKetOfBra
import AFTD.Kb.Tcs.InstInhabited
import AFTD.Kb.Tcs.InstFunLikeBraket

/-!
# Ket.PhaseEquiv

Topic: quantum   Node: 991ac9937c18

Provenance: formalization of a published result. Source: QuantumInfo, `Ket.PhaseEquiv`. Lean proof by Alex Meiburg, Rodolfo Soldati, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/States/Pure/Braket.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence relation on `Ket` where two kets equivalent if they are equal up to a global phase, i.e. `∃ z, ‖z‖ = 1 ∧ a.vec = z • b.vec
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
/-- The equivalence relation on `Ket` where two kets equivalent if they are equal up to a global phase, i.e. `∃ z, ‖z‖ = 1 ∧ a.vec = z • b.vec -/
noncomputable def Ket.PhaseEquiv : Setoid (Ket d) where
  r a b := ∃ z : ℂ, ‖z‖ = 1 ∧ a.vec = z • b.vec
  iseqv := {
    refl := fun x ↦ ⟨1, by simp⟩,
    symm := fun ⟨z,h₁,h₂⟩ ↦ ⟨conj z,
      by simp [h₁],
      by simp [h₁, h₂, smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]⟩,
    trans := fun ⟨z₁,h₁₁,h₁₂⟩ ⟨z₂,h₂₁,h₂₂⟩ ↦ ⟨z₁ * z₂,
      by simp [h₁₁, h₂₁],
      by simp [h₁₂, h₂₂, smul_smul]⟩
  }
