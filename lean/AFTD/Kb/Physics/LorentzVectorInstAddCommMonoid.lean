import AFTD.Prelude
import AFTD.Kb.Physics.LorentzVector

/-!
# Lorentz.Vector.instAddCommMonoid

Topic: special_relativity   Node: c408fc98a7a7

Provenance: formalization of a published result. Source: Physlib, `Lorentz.Vector.instAddCommMonoid`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.Vector.instAddCommMonoid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
noncomputable instance Lorentz.Vector.instAddCommMonoid {d} : AddCommMonoid (Vector d) :=
  inferInstanceAs (AddCommMonoid (Fin 1 ⊕ Fin d → ℝ))
