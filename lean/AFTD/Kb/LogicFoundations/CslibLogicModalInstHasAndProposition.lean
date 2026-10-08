import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicHasAnd
import AFTD.Kb.LogicFoundations.CslibLogicModalProposition
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasNotProposition

/-!
# Cslib.Logic.Modal.instHasAndProposition

Topic: proof_theory   Node: 61a8ebe340cd

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.Modal.instHasAndProposition`. Lean proof by Fabrizio Montesi, Marianna Girlando, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Modal/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.Modal.instHasAndProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.Modal.instHasAndProposition : HasAnd (Proposition Atom) := ⟨.and⟩
