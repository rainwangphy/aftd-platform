import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem

/-!
# Cslib.Logic.InferenceSystem.rwConclusion

Topic: proof_theory   Node: a8dd2906dd07

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.rwConclusion`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Rewrites the conclusion of a proof into an equal one.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Rewrites the conclusion of a proof into an equal one. -/
@[grind =]
def Cslib.Logic.InferenceSystem.rwConclusion [InferenceSystem S α] {Γ Δ : α} (h : Γ = Δ) (p : S⇓Γ) : S⇓Δ :=
  h ▸ p
