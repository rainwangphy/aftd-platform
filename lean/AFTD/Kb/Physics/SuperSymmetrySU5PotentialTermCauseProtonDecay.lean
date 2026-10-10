import AFTD.Prelude
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTerm
import AFTD.Kb.Physics.SuperSymmetrySU5PotentialTermInstDecidableInSuperPotential

/-!
# SuperSymmetry.SU5.PotentialTerm.causeProtonDecay

Topic: quantum_field_theory   Node: 2f1f0846a0fb

Provenance: formalization of a published result. Source: Physlib, `SuperSymmetry.SU5.PotentialTerm.causeProtonDecay`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finite set of terms in the superpotential and Kahler potential which are involved in proton decay. - `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` - `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` - `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd` - `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The finite set of terms in the superpotential and Kahler potential which are involved in proton decay. - `W¹ᵢⱼₖₗ 10ⁱ 10ʲ 10ᵏ 5̄Mˡ` - `𝜆ᵢⱼₖ 5̄Mⁱ 5̄Mʲ 10ᵏ` - `W²ᵢⱼₖ 10ⁱ 10ʲ 10ᵏ 5̄Hd` - `K¹ᵢⱼₖ 10ⁱ 10ʲ 5Mᵏ` -/
def SuperSymmetry.SU5.PotentialTerm.causeProtonDecay : Finset PotentialTerm :=
  {W1, Λ, W2, K1}
