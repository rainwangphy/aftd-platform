import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorEquivEuclid
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal

/-!
# Lorentz.Vector.eq_of_apply_eq

Topic: special_relativity   Node: c82c6f4e43a3

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.eq_of_apply_eq`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.eq_of_apply_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
@[ext]
lemma Lorentz.Vector.eq_of_apply_eq {d : ℕ} {v w : Vector d} (h : ∀ i, v i = w i) : v = w := by
  apply (equivEuclid d).injective
  ext i
  simpa using h i
