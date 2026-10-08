import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequent
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDual
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstBotProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstTopProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentAllQuest
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualSizeOf
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInj
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionDualInvolution
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasContextProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionPositiveDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionNegativeDecidable
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstHasHContextSequentProposition

/-!
# Cslib.Logic.CLL.Proof

Topic: proof_theory   Node: 9363ed5c1414

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.Proof`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A proof in the sequent calculus for classical linear logic.
-/

open Cslib.Logic.CLL
@[inherit_doc] local infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] local infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] local infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] local infix:30 " & " => Proposition.with
@[inherit_doc] local prefix:95 "!" => Proposition.bang
@[inherit_doc] local prefix:95 "ʔ" => Proposition.quest
open Cslib.Logic.CLL
@[inherit_doc] local postfix:max "⫠" => Proposition.dual

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib.Logic.CLL.Proposition in
/-- A proof in the sequent calculus for classical linear logic. -/
inductive Cslib.Logic.CLL.Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  | one : Proof {1}
  | bot : Proof Γ → Proof (⊥ ::ₘ Γ)
  | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
  | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Proof (a ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Proof (b ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | with : Proof (a ::ₘ Γ) → Proof (b ::ₘ Γ) → Proof ((a & b) ::ₘ Γ)
  | top : Proof (⊤ ::ₘ Γ)
  | quest : Proof (a ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
  | weaken : Proof Γ → Proof (ʔa ::ₘ Γ)
  | contract : Proof (ʔa ::ₘ ʔa ::ₘ Γ) → Proof (ʔa ::ₘ Γ)
  | bang {Γ : Sequent Atom} {a} : Γ.allQuest → Proof (a ::ₘ Γ) → Proof ((!a) ::ₘ Γ)
  -- No rule for zero.
