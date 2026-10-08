import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDerivableIn

/-!
# Cslib.Logic.InferenceSystem.DerivableIn.fromDerivation

Topic: proof_theory   Node: a930e4ced3d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.DerivableIn.fromDerivation`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shows derivability from a derivation.
-/

set_option quotPrecheck false
open Cslib Cslib.Logic Cslib.Logic.InferenceSystem
@[inherit_doc] local notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Shows derivability from a derivation. -/
theorem Cslib.Logic.InferenceSystem.DerivableIn.fromDerivation [InferenceSystem S α] {a : α} (d : S⇓a) : DerivableIn S a :=
  Nonempty.intro d
