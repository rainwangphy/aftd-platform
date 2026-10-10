import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoVector
import AFTD.Kb.Physics.LorentzCoVectorInstNorm
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoVectorInstModuleReal
import AFTD.Kb.Physics.LorentzCoVectorEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorNormEqEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorInstFiniteDimensionalReal

/-!
# Lorentz.CoVector.isNormedAddCommGroup

Topic: special_relativity   Node: fdd1c3824a41

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.isNormedAddCommGroup`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.CoVector.isNormedAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
noncomputable instance Lorentz.CoVector.isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (CoVector d) where
  dist_self x := by simp [norm_eq_equivEuclid]
  dist_comm x y := by
    simpa [norm_eq_equivEuclid, ← dist_eq_norm_neg_add] using
      dist_comm (equivEuclid d x) (equivEuclid d y)
  dist_triangle x y z := by
    simpa [norm_eq_equivEuclid, ← dist_eq_norm_neg_add] using dist_triangle
      ((equivEuclid d) x) ((equivEuclid d) y) ((equivEuclid d) z)
  eq_of_dist_eq_zero {x y} := by
    simp only [norm_eq_equivEuclid, map_add]
    intro h
    apply (equivEuclid d).injective
    simp at h
    rw [← neg_add_eq_zero, h]
