import AFTD.Prelude

/-!
# StandardModel.fundamentalSU2

Topic: quantum_field_theory   Node: 3f81485a2d74

Provenance: formalization of a published result. Source: Physlib, `StandardModel.fundamentalSU2`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Representations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The fundamental representation of SU(2) as a homomorphism to `unitaryGroup (Fin 2) ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The fundamental representation of SU(2) as a homomorphism to `unitaryGroup (Fin 2) ℂ`. -/
@[simps!]
def StandardModel.fundamentalSU2 : specialUnitaryGroup (Fin 2) ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := ⟨g.1, g.prop.1⟩
  map_mul' _ _ := Subtype.ext rfl
  map_one' := Subtype.ext rfl
