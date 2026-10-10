import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetricRealNumericalRange
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapNumericalRangeNeg
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapIsSymmetricRealNumericalRangeEq

/-!
# LinearPMap.IsSymmetric.realNumericalRange_neg

Topic: quantum_mechanics   Node: 89b6a97c1094

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.realNumericalRange_neg`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Symmetric.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.realNumericalRange_neg
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
@[simp]
lemma LinearPMap.IsSymmetric.realNumericalRange_neg (T : H →ₗ.[ℂ] H) : Θᵣₑ (-T) = -Θᵣₑ T := by
  ext
  simp [realNumericalRange_eq, neg_eq_iff_eq_neg]
