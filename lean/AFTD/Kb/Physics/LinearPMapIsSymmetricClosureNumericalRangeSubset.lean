import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapIsSymmetricNumericalRangeSubset
import AFTD.Kb.Physics.LinearPMapIsSymmetricRealNumericalRangeNeg

/-!
# LinearPMap.IsSymmetric.closure_numericalRange_subset

Topic: quantum_mechanics   Node: ac83959d586b

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.closure_numericalRange_subset`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Symmetric.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.closure_numericalRange_subset
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
lemma LinearPMap.IsSymmetric.closure_numericalRange_subset : _root_.closure (Θ T) ⊆ range ofReal :=
  (closure_mono hT.numericalRange_subset).trans
    Complex.isometry_ofReal.isClosedEmbedding.isClosed_range.closure_subset
