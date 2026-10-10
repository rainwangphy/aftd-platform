import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzVectorInstModuleReal
import AFTD.Kb.Physics.LorentzVectorEquivEuclidApply
import AFTD.Kb.Physics.LorentzVectorAbsComponentLeNorm
import AFTD.Kb.Physics.LorentzVectorInstFiniteDimensionalReal
import AFTD.Kb.Physics.LorentzVectorInstNorm
import AFTD.Kb.Physics.LorentzVectorIsNormedAddCommGroup
import AFTD.Kb.Physics.LorentzVectorIsNormedSpace
import AFTD.Kb.Physics.LorentzVectorInstInnerReal
import AFTD.Kb.Physics.LorentzVectorInnerProductSpace
import AFTD.Kb.Physics.LorentzVectorInstChartedSpace
import AFTD.Kb.Physics.LorentzVectorInstCoeFunForallSumFinOfNatNatReal

/-!
# Lorentz.Vector.apply_smul

Topic: special_relativity   Node: 7c7f9c7f602f

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.apply_smul`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.apply_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open InnerProductSpace in
@[simp]
lemma Lorentz.Vector.apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl
