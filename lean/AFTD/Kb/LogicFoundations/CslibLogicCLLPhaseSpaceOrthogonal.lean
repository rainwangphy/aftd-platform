import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpace
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceImp

/-!
# Cslib.Logic.CLL.PhaseSpace.orthogonal

Topic: proof_theory   Node: ffc69aa1d895

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace.orthogonal`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The orthogonal `X⫠` of a set X: the set of elements that map X into ⊥ under multiplication.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Logic Cslib.Logic.CLL Cslib.Logic.CLL.PhaseSpace in
universe u v in
open scoped Pointwise in
open Set in
attribute [local grind _=_] Set.le_iff_subset in
variable {P : Type*} [PhaseSpace P] {p q : P} in
/-- The orthogonal `X⫠` of a set X: the set of elements that map X into ⊥ under multiplication. -/
def Cslib.Logic.CLL.PhaseSpace.orthogonal (G : Set P) : Set P :=
  imp G PhaseSpace.bot
