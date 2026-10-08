import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem

/-!
# Cslib.Logic.InferenceSystem.DerivableIn

Topic: proof_theory   Node: 850b5928178e

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.DerivableIn`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`a` is derivable in `S` if it is the conclusion of some derivation.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `a` is derivable in `S` if it is the conclusion of some derivation. -/
def Cslib.Logic.InferenceSystem.DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)
