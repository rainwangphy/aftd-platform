import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapIsSymmetricImEqZeroOfMemNumericalRange
import AFTD.Kb.Physics.LinearPMapIsSymmetricRealNumericalRangeNeg

/-!
# LinearPMap.IsSymmetric.numericalRange_subset

Topic: quantum_mechanics   Node: bb1aa56b7c98

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.numericalRange_subset`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Symmetric.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The numerical range of a symmetric operator is contained in the real axis.
-/

set_option quotPrecheck false
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
variable {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) in
include hT in
/-- The numerical range of a symmetric operator is contained in the real axis. -/
lemma LinearPMap.IsSymmetric.numericalRange_subset : Θ T ⊆ range ofReal :=
  fun z hz ↦ ⟨z.re, Complex.ext rfl (hT.im_eq_zero_of_mem_numericalRange hz).symm⟩
