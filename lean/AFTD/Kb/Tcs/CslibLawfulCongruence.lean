import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCongruence
import AFTD.Kb.Tcs.CslibHasContext
import AFTD.Kb.Tcs.CslibHasContextContext
import AFTD.Kb.Tcs.CslibHasHContext
import AFTD.Kb.Tcs.CslibCongruenceR
import AFTD.Kb.Tcs.CslibInstCongruenceOfDefaultCongruence
import AFTD.Kb.LogicFoundations.CslibLogicCLLPropositionContextFill
import AFTD.Kb.LogicFoundations.CslibLogicCLLSequentContextFill
import AFTD.Kb.Tcs.CslibDefaultCongruenceR

/-!
# Cslib.LawfulCongruence

Topic: computability   Node: c58aa71cae17

Provenance: formalization of a published result. Source: CSLib, `Cslib.LawfulCongruence`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence relation on `α` preserved by all contexts.
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

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An equivalence relation on `α` preserved by all contexts. -/
class Cslib.LawfulCongruence (r : α → α → Prop) [Congruence r] [HasContext α] extends
  IsEquiv α r, covariant : CovariantClass (HasContext.Context α) α (·<[·]) (· ≡[r] ·)
