import AFTD.Prelude

/-!
# StandardModel.gaugeGroupℤ₂RootToℤ₆Root

Topic: quantum_field_theory   Node: d06fbaf09855

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₂RootToℤ₆Root`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of second roots of unity into sixth roots of unity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The inclusion of second roots of unity into sixth roots of unity. -/
noncomputable def StandardModel.gaugeGroupℤ₂RootToℤ₆Root : rootsOfUnity 2 ℂ →* rootsOfUnity 6 ℂ :=
  Subgroup.inclusion (rootsOfUnity_le_of_dvd (by norm_num : 2 ∣ 6))
