import AFTD.Prelude

/-!
# Option.toFinset_inj

Topic: quantum_field_theory   Node: 40a98a4d01bb

Provenance: formalization of a published result. Source: Physlib, `Option.toFinset_inj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Option.toFinset_inj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓩 : Type} in
lemma Option.toFinset_inj {x y : Option 𝓩} :
    x = y ↔ x.toFinset = y.toFinset := by
  cases x <;> cases y <;> simp [Option.toFinset]
