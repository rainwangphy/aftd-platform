import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrum
import AFTD.Kb.Physics.SuperSymmetrySU5ChargeSpectrumEqIff

/-!
# SuperSymmetry.SU5.ChargeSpectrum.instDecidableEq

Topic: quantum_field_theory   Node: 87941ffe3ced

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.instDecidableEq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SuperSymmetry.SU5.ChargeSpectrum.instDecidableEq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SuperSymmetry SuperSymmetry.SU5 SuperSymmetry.SU5.ChargeSpectrum in
variable {𝓩 : Type} in
instance SuperSymmetry.SU5.ChargeSpectrum.instDecidableEq [DecidableEq 𝓩] : DecidableEq (ChargeSpectrum 𝓩) := fun _ _ =>
  decidable_of_iff _ eq_iff.symm
