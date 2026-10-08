import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpace

/-!
# Cslib.Logic.CLL.PhaseSpace.imp

Topic: proof_theory   Node: 5ead94c5c985

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace.imp`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Implication between two setsin a phase space: the set of elements m such that for all x ∈ X, we have m * x ∈ Y.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Logic Cslib.Logic.CLL in
universe u v in
open scoped Pointwise in
open Set in
attribute [local grind _=_] Set.le_iff_subset in
variable {P : Type*} [PhaseSpace P] {p q : P} in
/-- Implication between two setsin a phase space: the set of elements m such that for all x ∈ X, we have m * x ∈ Y. -/
def Cslib.Logic.CLL.PhaseSpace.imp [PhaseSpace M] (X Y : Set M) : Set M := {m | ∀ x ∈ X, m * x ∈ Y}
