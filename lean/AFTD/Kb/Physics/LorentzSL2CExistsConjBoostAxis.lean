import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CBoostAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CBoostAxisEqConj
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoInvApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CBoostAxisTwoApply

/-!
# Lorentz.SL2C.exists_conj_boostAxis

Topic: special_relativity   Node: dbda627d61c1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.exists_conj_boostAxis`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzGroup/Boosts/Axis.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every coordinate-axis boost is conjugate to the `z`-axis boost.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- Every coordinate-axis boost is conjugate to the `z`-axis boost. -/
lemma Lorentz.SL2C.exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  exact ⟨rotationZToAxis i, fun t ht => boostAxis_eq_conj i t ht⟩
