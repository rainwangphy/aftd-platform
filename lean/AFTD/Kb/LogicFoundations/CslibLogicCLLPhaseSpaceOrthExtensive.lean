import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpace
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceOrthogonal
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceOrthogonalDef
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual

/-!
# Cslib.Logic.CLL.PhaseSpace.orth_extensive

Topic: proof_theory   Node: e8ba418973d2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace.orth_extensive`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.CLL Cslib.Logic.CLL.PhaseSpace
@[inherit_doc] local postfix:max "⫠" => orthogonal
open Cslib Cslib.Logic Cslib.Logic.CLL
@[inherit_doc] local postfix:max "⫠" => Proposition.dual

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Logic Cslib.Logic.CLL Cslib.Logic.CLL.PhaseSpace in
universe u v in
open scoped Pointwise in
open Set in
attribute [local grind _=_] Set.le_iff_subset in
variable {P : Type*} [PhaseSpace P] {p q : P} in
/-- The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X. -/
lemma Cslib.Logic.CLL.PhaseSpace.orth_extensive (X : Set P) : X ⊆ X⫠⫠ := by grind
