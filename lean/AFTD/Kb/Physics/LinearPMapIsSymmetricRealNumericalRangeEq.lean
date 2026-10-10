import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetricRealNumericalRange
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.IsSymmetric.realNumericalRange_eq

Topic: quantum_mechanics   Node: 57e10f34d71f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.realNumericalRange_eq`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Symmetric.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.realNumericalRange_eq
-/

set_option quotPrecheck false
open LinearPMap LinearPMap.IsSymmetric
@[inherit_doc realNumericalRange]
local notation "Θᵣₑ" => realNumericalRange
open LinearPMap
@[inherit_doc numericalRange]
local notation "Θ" => numericalRange

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap LinearPMap.IsSymmetric in
open InnerProductSpace in
open Complex in
open Set in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
lemma LinearPMap.IsSymmetric.realNumericalRange_eq (T : H →ₗ.[ℂ] H) : Θᵣₑ T = re '' Θ T := rfl
