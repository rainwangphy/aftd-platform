import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorEquivEuclid
import AFTD.Kb.Physics.LorentzVectorNormEqEquivEuclid
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorAbsComponentLeNorm
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal

/-!
# Lorentz.Vector.isNormedAddCommGroup

Topic: special_relativity   Node: 07f0b62f89a1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.isNormedAddCommGroup`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.isNormedAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
noncomputable instance Lorentz.Vector.isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) where
  dist_self x := by simp [norm_eq_equivEuclid]
  dist_comm x y := by
    simpa [norm_eq_equivEuclid, dist_eq_norm_neg_add] using dist_comm ((equivEuclid d) x) _
  dist_triangle x y z := by
    simpa [norm_eq_equivEuclid, dist_eq_norm_neg_add] using dist_triangle
      ((equivEuclid d) x) ((equivEuclid d) y) ((equivEuclid d) z)
  eq_of_dist_eq_zero {x y} := by
    simp only [norm_eq_equivEuclid, map_add]
    intro h
    apply (equivEuclid d).injective
    simp at h
    rw [← neg_add_eq_zero, h]
