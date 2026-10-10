import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector
import AFTD.Kb.Physics.LorentzVectorInstAddCommMonoid

/-!
# Lorentz.Vector.instModuleReal

Topic: special_relativity   Node: 17e62b055151

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.instModuleReal`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.instModuleReal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
noncomputable instance Lorentz.Vector.instModuleReal {d} : Module ℝ (Vector d) :=
  inferInstanceAs (Module ℝ (Fin 1 ⊕ Fin d → ℝ))
