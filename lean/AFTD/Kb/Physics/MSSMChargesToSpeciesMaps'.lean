import AFTD.Prelude

/-!
# MSSMCharges.toSpeciesMaps'

Topic: quantum_field_theory   Node: 98537d42d2ad

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.toSpeciesMaps'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `(Fin 18 → ℚ)` and `(Fin 6 → Fin 3 → ℚ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- An equivalence between `(Fin 18 → ℚ)` and `(Fin 6 → Fin 3 → ℚ)`. -/
@[simps!]
def MSSMCharges.toSpeciesMaps' : (Fin 18 → ℚ) ≃ (Fin 6 → Fin 3 → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans
    ((@finProdFinEquiv 6 3).arrowCongr (Equiv.refl ℚ))).symm
