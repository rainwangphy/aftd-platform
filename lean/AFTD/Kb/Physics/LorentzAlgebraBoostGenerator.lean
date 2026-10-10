import AFTD.Prelude

/-!
# lorentzAlgebra.boostGenerator

Topic: special_relativity   Node: d1922617c098

Provenance: formalization of a published result. Source: Physlib, `lorentzAlgebra.boostGenerator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzAlgebra/Basis.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The boost generator K_i in the Lorentz algebra so(1,3). This matrix generates infinitesimal Lorentz boosts in the i-th spatial direction. The matrix has non-zero entries only at positions (0, i+1) and (i+1, 0) with value 1, where we use the index convention 0 = time, 1,2,3 = space. ## Properties - Symmetric: K_iᵀ = K_i - Traceless: tr(K_i) = 0 - Satisfies Lorentz algebra condition: K_iᵀ η = -η K_i ## Physical Meaning Exponentiating β·K_i produces a finite Lorentz boost with rapidity β in direction i.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The boost generator K_i in the Lorentz algebra so(1,3). This matrix generates infinitesimal Lorentz boosts in the i-th spatial direction. The matrix has non-zero entries only at positions (0, i+1) and (i+1, 0) with value 1, where we use the index convention 0 = time, 1,2,3 = space. ## Properties - Symmetric: K_iᵀ = K_i - Traceless: tr(K_i) = 0 - Satisfies Lorentz algebra condition: K_iᵀ η = -η K_i ## Physical Meaning Exponentiating β·K_i produces a finite Lorentz boost with rapidity β in direction i. -/
def lorentzAlgebra.boostGenerator (i : Fin 3) : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  fun μ ν =>
    if (μ = Sum.inl 0 ∧ ν = Sum.inr i) ∨ (μ = Sum.inr i ∧ ν = Sum.inl 0) then 1
    else 0
