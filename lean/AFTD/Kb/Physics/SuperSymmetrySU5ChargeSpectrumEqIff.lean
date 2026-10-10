import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrum
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrumEqOfParts

/-!
# SuperSymmetry.SU5.ChargeSpectrum.eq_iff

Topic: quantum_field_theory   Node: 2f1c8efa0737

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.eq_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.ChargeSpectrum.eq_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SuperSymmetry SuperSymmetry.SU5 SuperSymmetry.SU5.ChargeSpectrum in
variable {𝓩 : Type} in
lemma SuperSymmetry.SU5.ChargeSpectrum.eq_iff {x y : ChargeSpectrum 𝓩} :
    x = y ↔ x.qHd = y.qHd ∧ x.qHu = y.qHu ∧ x.Q5 = y.Q5 ∧ x.Q10 = y.Q10 :=
  ⟨fun h => ⟨congrArg qHd h, congrArg qHu h, congrArg Q5 h, congrArg Q10 h⟩,
    fun ⟨h1, h2, h3, h4⟩ => eq_of_parts h1 h2 h3 h4⟩
