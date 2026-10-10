import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorEquivEuclid
import AFTD.Kb.Physics.LorentzVectorInnerEqEquivEuclid
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorAbsComponentLeNorm
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace

/-!
# Lorentz.Vector.inner_eq_sum

Topic: special_relativity   Node: 7e85d6033748

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.inner_eq_sum`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inner product on `Vector d` as a sum over components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
/-- The inner product on `Vector d` as a sum over components. -/
lemma Lorentz.Vector.inner_eq_sum {d : ℕ} (v w : Vector d) : ⟪v, w⟫_ℝ = ∑ μ, v μ * w μ := by
  rw [inner_eq_equivEuclid, PiLp.inner_apply]
  simp [mul_comm]
