import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoVector
import AFTD.Kb.Physics.LorentzCoVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzCoVectorInstInnerReal
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoVectorInstModuleReal
import AFTD.Kb.Physics.LorentzCoVectorEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorInnerEqEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorNormEqEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzCoVectorInstNorm

/-!
# Lorentz.CoVector.innerProductSpace

Topic: special_relativity   Node: 12bd4b6a1dfb

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.innerProductSpace`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Euclidean inner product structure on `CoVector`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
/-- The Euclidean inner product structure on `CoVector`. -/
noncomputable instance Lorentz.CoVector.innerProductSpace (d : ℕ) : InnerProductSpace ℝ (CoVector d) where
  norm_sq_eq_re_inner v := by
    simp only [inner_eq_equivEuclid, norm_eq_equivEuclid]
    exact InnerProductSpace.norm_sq_eq_re_inner (equivEuclid d v)
  conj_inner_symm x y := by
    simp only [inner_eq_equivEuclid]
    exact InnerProductSpace.conj_inner_symm (equivEuclid d x) (equivEuclid d y)
  add_left x y z := by
    simp only [inner_eq_equivEuclid, map_add]
    exact InnerProductSpace.add_left (equivEuclid d x) (equivEuclid d y) (equivEuclid d z)
  smul_left x y r := by
    simp only [inner_eq_equivEuclid, map_smul]
    exact InnerProductSpace.smul_left (equivEuclid d x) (equivEuclid d y) r
