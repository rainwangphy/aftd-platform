import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasContext
import AFTD.Kb.Tcs.CslibCongruence
import AFTD.Kb.Tcs.CslibHasHContext
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.Tcs.CslibLawfulCongruence
import AFTD.Kb.Tcs.CslibCongruenceR
import AFTD.Kb.Tcs.CslibHasContextContext
import AFTD.Kb.Tcs.CslibInstCongruenceOfDefaultCongruence
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContextFill
import AFTD.Kb.Tcs.CslibDefaultCongruenceR

/-!
# Cslib.Logic.LogicalEquivalence

Topic: proof_theory   Node: 2d98889cfb31

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.LogicalEquivalence`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/LogicalEquivalence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A logical equivalence `eqv` for an inference system `S` is a congruence on propositions (of type `α`) that preserves validity of judgements under any judgemental context.
-/

set_option quotPrecheck false
open Cslib
@[inherit_doc]
local notation:29 a " ≡[" r "] " b => Congruence.r r a b
open Cslib
@[inherit_doc]
local infix:29 " ≡ " => DefaultCongruence.r
open Cslib
@[inherit_doc] local notation:max c "<[" t "]" => HasHContext.fill c t
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation "⇓" a:90 => InferenceSystem.derivation Default a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A logical equivalence `eqv` for an inference system `S` is a congruence on propositions (of type `α`) that preserves validity of judgements under any judgemental context. -/
class Cslib.Logic.LogicalEquivalence S (eqv : α → α → Prop)
    [HasContext α] [Congruence eqv] [HasHContext Judgement α] [InferenceSystem S Judgement]
    extends LawfulCongruence eqv where
  /-- Validity is preserved for any judgemental context. -/
  eqvFillValid (heqv : a ≡[eqv] b) (c : HasHContext.Context Judgement α)
    (h : S⇓(c<[a])) : S⇓(c<[b])
