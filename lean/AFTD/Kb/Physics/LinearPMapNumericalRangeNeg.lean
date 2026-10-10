import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapNumericalRange
import AFTD.Kb.Physics.LinearPMapNumericalRangeEq

/-!
# LinearPMap.numericalRange_neg

Topic: quantum_mechanics   Node: 85f0cb196776

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.numericalRange_neg`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.numericalRange_neg
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc numericalRange]
local notation "Θ" => numericalRange

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
@[simp]
lemma LinearPMap.numericalRange_neg (T : H →ₗ.[ℂ] H) : Θ (-T) = -Θ T := by
  ext
  simp [numericalRange_eq, neg_eq_iff_eq_neg]
