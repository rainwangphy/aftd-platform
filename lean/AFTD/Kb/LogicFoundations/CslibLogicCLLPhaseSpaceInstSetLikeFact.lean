import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpace
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceFact
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceOrthogonalDef

/-!
# Cslib.Logic.CLL.PhaseSpace.instSetLikeFact

Topic: proof_theory   Node: afa3c9c4b6f9

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace.instSetLikeFact`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.Logic.CLL.PhaseSpace.instSetLikeFact
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Logic Cslib.Logic.CLL Cslib.Logic.CLL.PhaseSpace in
universe u v in
open scoped Pointwise in
open Set in
attribute [local grind _=_] Set.le_iff_subset in
variable {P : Type*} [PhaseSpace P] {p q : P} in
set_option linter.tacticAnalysis.verifyGrindOnly false in
instance Cslib.Logic.CLL.PhaseSpace.instSetLikeFact : SetLike (Fact P) P where
  coe := Fact.carrier
  coe_injective _ _ _ := by grind only [cases Fact]
