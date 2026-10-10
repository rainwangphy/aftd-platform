import AFTD.Prelude
import AFTD.Kb.Physics.LinearMapMapSmulOfCommutesI

/-!
# LinearMap.commutesI_of_basis

Topic: classical_mechanics   Node: 33339a54a4e2

Provenance: formalization of a published result. Source: Physlib, `LinearMap.commutesI_of_basis`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/ComplexLinear.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `ℝ`-linear map commuting with `i` on a `ℂ`-basis commutes with `i` everywhere.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearMap in
variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E] in
/-- An `ℝ`-linear map commuting with `i` on a `ℂ`-basis commutes with `i` everywhere. -/
lemma LinearMap.commutesI_of_basis {ι : Type*} [Fintype ι] (L : V →ₗ[ℝ] E) (b : Module.Basis ι ℂ V)
    (h : ∀ i, L (Complex.I • b i) = Complex.I • L (b i)) (v : V) :
    L (Complex.I • v) = Complex.I • L v := by
  rw [← b.sum_repr v, Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, map_smul_of_commutesI L (h i), map_smul_of_commutesI L (h i), smul_smul,
    mul_comm]
