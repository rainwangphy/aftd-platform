import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystem
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDefault
import AFTD.Kb.LogicFoundations.CslibLogicInferenceSystemDerivableIn

/-!
# Cslib.Logic.InferenceSystem.Derivable

Topic: proof_theory   Node: 7301e7accf01

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.Derivable`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`a : α` is derivable in the default inference system for `α`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `a : α` is derivable in the default inference system for `α`. -/
abbrev Cslib.Logic.InferenceSystem.Derivable [InferenceSystem Default α] := DerivableIn Default (α := α)
