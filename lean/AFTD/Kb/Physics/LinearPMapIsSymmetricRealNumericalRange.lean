import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.IsSymmetric.realNumericalRange

Topic: quantum_mechanics   Node: 4fd4643fce31

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.realNumericalRange`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Symmetric.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The projection of the numerical range onto the real axis.
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc numericalRange]
local notation "Θ" => numericalRange

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
open Complex in
open Set in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The projection of the numerical range onto the real axis. -/
def LinearPMap.IsSymmetric.realNumericalRange (T : H →ₗ.[ℂ] H) : Set ℝ := re '' (Θ T)
