import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpace
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceOrthogonal
import AFTD.Kb.LogicFoundations.CslibLogicCLLPhaseSpaceOrthogonalDef
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual

/-!
# Cslib.Logic.CLL.PhaseSpace.orth_iUnion

Topic: proof_theory   Node: 3b62d92003e5

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace.orth_iUnion`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Given a phase space (P, ⊥) and a set of subsets (Gᵢ)_{i ∈ I} of P, we have that (⋃ᵢ Gᵢ)⫠ = ⋂ᵢ Gᵢ⫠.
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
/-- Given a phase space (P, ⊥) and a set of subsets (Gᵢ)_{i ∈ I} of P, we have that (⋃ᵢ Gᵢ)⫠ = ⋂ᵢ Gᵢ⫠. -/
lemma Cslib.Logic.CLL.PhaseSpace.orth_iUnion {ι : Sort*} (G : ι → Set P) :
    (⋃ i, G i)⫠ = ⋂ i, (G i)⫠ := by
  ext m; constructor
  · intro hm
    have hm' : ∀ x ∈ ⋃ j, G j, m * x ∈ PhaseSpace.bot := by grind
    refine mem_iInter.mpr (fun i => ?_)
    exact fun x hx => hm' x (mem_iUnion.mpr ⟨i, hx⟩)
  · intro hm x hx
    rcases mem_iUnion.mp hx with ⟨i, hix⟩
    have hmi : m ∈ (G i)⫠ := mem_iInter.mp hm i
    grind
