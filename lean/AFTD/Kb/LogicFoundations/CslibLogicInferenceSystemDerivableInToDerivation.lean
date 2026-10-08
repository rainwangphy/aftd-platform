import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDerivableIn
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemInstCoeDerivationDerivableIn

/-!
# Cslib.Logic.InferenceSystem.DerivableIn.toDerivation

Topic: proof_theory   Node: ed9fe43fd5db

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.DerivableIn.toDerivation`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extracts (noncomputably) a derivation from the fact that a conclusion is derivable.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Extracts (noncomputably) a derivation from the fact that a conclusion is derivable. -/
noncomputable def Cslib.Logic.InferenceSystem.DerivableIn.toDerivation [InferenceSystem S α] {a : α} (d : DerivableIn S a) :
    S⇓a :=
  Classical.choice d
