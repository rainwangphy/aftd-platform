import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.raw_commutator_eq_of_symmetric

Topic: quantum_mechanics   Node: c66827452f3f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.raw_commutator_eq_of_symmetric`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Uncertainty.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.raw_commutator_eq_of_symmetric
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.raw_commutator_eq_of_symmetric
    (A B : H →ₗ.[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (ψ : A.domain) (hψB : (ψ : H) ∈ B.domain)
    (hBA : A ψ ∈ B.domain) (hAB : B ⟨ψ, hψB⟩ ∈ A.domain)
    {c : ℝ}
    (h_raw : ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ = Complex.I * c) :
    ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ - ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ = Complex.I * c := by
  have ha_pairing :
      ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ = ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ := by
    exact hA ψ ⟨B ⟨ψ, hψB⟩, hAB⟩
  have hb_pairing :
      ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ = ⟪(ψ : H), B ⟨A ψ, hBA⟩⟫_ℂ := by
    exact hB ⟨ψ, hψB⟩ ⟨A ψ, hBA⟩
  calc
    ⟪A ψ, B ⟨ψ, hψB⟩⟫_ℂ - ⟪B ⟨ψ, hψB⟩, A ψ⟫_ℂ =
      ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩⟫_ℂ -
        ⟪(ψ : H), B ⟨A ψ, hBA⟩⟫_ℂ := by
          rw [ha_pairing, hb_pairing]
    _ = ⟪(ψ : H), A ⟨B ⟨ψ, hψB⟩, hAB⟩ - B ⟨A ψ, hBA⟩⟫_ℂ := by
          rw [inner_sub_right]
    _ = Complex.I * c := h_raw
