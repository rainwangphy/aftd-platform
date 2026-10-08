import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDerivableIn
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDerivableInFromDerivation

/-!
# Cslib.Logic.InferenceSystem.instCoeDerivationDerivableIn

Topic: proof_theory   Node: 8f4b02dd3471

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.instCoeDerivationDerivableIn`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.InferenceSystem.instCoeDerivationDerivableIn
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.InferenceSystem.instCoeDerivationDerivableIn [InferenceSystem S α] {a : α} : Coe (S⇓a) (DerivableIn S a) := ⟨DerivableIn.fromDerivation⟩
