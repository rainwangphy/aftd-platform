import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDefault

/-!
# Cslib.Logic.HasInferenceSystem

Topic: proof_theory   Node: 8a04bdcb9c04

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasInferenceSystem`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Class for types (`α`) that have a canonical inference system.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Class for types (`α`) that have a canonical inference system. -/
abbrev Cslib.Logic.HasInferenceSystem := InferenceSystem InferenceSystem.Default
