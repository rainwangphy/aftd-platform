import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeyl

/-!
# Fermion.Dirac

Topic: special_relativity   Node: b5e411c4ca1a

Provenance: formalization of a published result. Source: Physlib, `Fermion.Dirac`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Dirac/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Dirac fermion, consisting of a left handed Weyl fermion and a dual right handed Weyl fermion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- A Dirac fermion, consisting of a left handed Weyl fermion and a dual right handed Weyl fermion. -/
structure Fermion.Dirac where
  /-- The left handed component of the Dirac fermion. -/
  left : LeftHandedWeyl
  /-- The right handed component of the Dirac fermion. -/
  dualRight : DualRightHandedWeyl
