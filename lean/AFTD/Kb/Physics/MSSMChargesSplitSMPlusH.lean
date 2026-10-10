import AFTD.Prelude

/-!
# MSSMCharges.splitSMPlusH

Topic: quantum_field_theory   Node: 1d0ad1e2f4ff

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.splitSMPlusH`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `Fin 18 ⊕ Fin 2 → ℚ` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- An equivalence between `Fin 18 ⊕ Fin 2 → ℚ` and `(Fin 18 → ℚ) × (Fin 2 → ℚ)`. -/
@[simps!]
def MSSMCharges.splitSMPlusH : (Fin 18 ⊕ Fin 2 → ℚ) ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) where
  toFun f := (f ∘ Sum.inl, f ∘ Sum.inr)
  invFun f := Sum.elim f.1 f.2
  left_inv f := Sum.elim_comp_inl_inr f
  right_inv _ := rfl
