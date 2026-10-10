import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrum
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrumInstDecidableEq

/-!
# SuperSymmetry.SU5.ChargeSpectrum.toProd

Topic: quantum_field_theory   Node: ece53c2d0e86

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.toProd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The explicit casting of a term of type `Charges 𝓩` to a term of `Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SuperSymmetry SuperSymmetry.SU5 in
variable {𝓩 : Type} in
/-- The explicit casting of a term of type `Charges 𝓩` to a term of `Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩`. -/
def SuperSymmetry.SU5.ChargeSpectrum.toProd : ChargeSpectrum 𝓩 ≃ Option 𝓩 × Option 𝓩 × Finset 𝓩 × Finset 𝓩 where
  toFun x := (x.qHd, x.qHu, x.Q5, x.Q10)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
