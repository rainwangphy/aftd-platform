import AFTD.Prelude

/-!
# UnitaryOneParameterGroup

Topic: classical_mechanics   Node: 1c45cd93c3e2

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A norm-continuous unitary one-parameter group on a complex Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A norm-continuous unitary one-parameter group on a complex Hilbert space. -/
structure UnitaryOneParameterGroup (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The additive character from the real parameter to unitary operators. -/
  toAddChar : AddChar ℝ (H →L[ℂ] H)
  /-- The group is valued in the unitary operators on `H`. -/
  mem_unitary : ∀ t, toAddChar t ∈ unitary (H →L[ℂ] H)
  /-- The group is continuous in the operator norm. -/
  continuous : Continuous toAddChar

attribute [coe] UnitaryOneParameterGroup.toAddChar
