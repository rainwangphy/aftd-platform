import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CBoostAxis
import AFTD.Kb.Physics.LorentzSL2CBoostAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisTwoApply

/-!
# Lorentz.SL2C.boostAxis_conjTranspose

Topic: special_relativity   Node: 3d3fdcbe138c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.boostAxis_conjTranspose`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix underlying an axis-boost lift is Hermitian.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The matrix underlying an axis-boost lift is Hermitian. -/
lemma Lorentz.SL2C.boostAxis_conjTranspose (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht).1ᴴ = (boostAxis i t ht).1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [boostAxis]
