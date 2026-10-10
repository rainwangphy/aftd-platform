import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrum

/-!
# SuperSymmetry.SU5.ChargeSpectrum.eq_of_parts

Topic: quantum_field_theory   Node: 7129dffa4190

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.eq_of_parts`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.ChargeSpectrum.eq_of_parts
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SuperSymmetry SuperSymmetry.SU5 in
variable {𝓩 : Type} in
lemma SuperSymmetry.SU5.ChargeSpectrum.eq_of_parts {x y : ChargeSpectrum 𝓩} (h1 : x.qHd = y.qHd) (h2 : x.qHu = y.qHu)
    (h3 : x.Q5 = y.Q5) (h4 : x.Q10 = y.Q10) : x = y := by
  cases x
  cases y
  simp_all
