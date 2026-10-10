import AFTD.Prelude

/-!
# SuperSymmetry.SU5.ChargeSpectrum.ofFinsetCard

Topic: quantum_field_theory   Node: 6f0f85c62fa0

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.ChargeSpectrum.ofFinsetCard`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cardinality of `ofFinset S5 S10`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓩 : Type} in
variable [DecidableEq 𝓩] in
/-- The cardinality of `ofFinset S5 S10`. -/
def SuperSymmetry.SU5.ChargeSpectrum.ofFinsetCard (S5 S10 : Finset 𝓩) : ℕ :=
    (S5.card + 1) * (S5.card + 1) * (2 ^ S5.card : ℕ) * (2 ^ S10.card : ℕ)
