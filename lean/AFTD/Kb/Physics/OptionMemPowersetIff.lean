import AFTD.Prelude
import AFTD.Kb.Physics.OptionPowerset

/-!
# Option.mem_powerset_iff

Topic: quantum_field_theory   Node: 828def71b468

Provenance: formalization of a published result. Source: Physlib, `Option.mem_powerset_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Option.mem_powerset_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓩 : Type} in
variable [DecidableEq 𝓩] in
@[simp]
lemma Option.mem_powerset_iff {x : Option 𝓩} (y : Option 𝓩) :
    y ∈ x.powerset ↔ y.toFinset ⊆ x.toFinset := by
  cases x <;> cases y <;> simp [Option.powerset]
