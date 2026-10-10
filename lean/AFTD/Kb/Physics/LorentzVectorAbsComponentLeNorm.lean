import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorEquivEuclid
import AFTD.Kb.Physics.LorentzVectorNormEqEquivEuclid
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal

/-!
# Lorentz.Vector.abs_component_le_norm

Topic: special_relativity   Node: 0f8cb864375f

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.abs_component_le_norm`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.abs_component_le_norm
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
@[simp]
lemma Lorentz.Vector.abs_component_le_norm {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    |v i| ≤ ‖v‖ := by
  simp [norm_eq_equivEuclid, PiLp.norm_eq_of_L2, -Fintype.sum_sum_type]
  refine Real.abs_le_sqrt ?_
  trans ∑ j ∈ {i}, (v j) ^ 2
  · simp
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)
