import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicModalProposition
import AFTD.Kb.LogicFoundations.CslibLogicHasAnd
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasAndProposition
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasNotProposition
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasDiamondProposition

/-!
# Cslib.Logic.Modal.Proposition.and_def

Topic: proof_theory   Node: 476a71adab8f

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.Modal.Proposition.and_def`. Lean proof by Fabrizio Montesi, Marianna Girlando, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Modal/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.Modal.Proposition.and_def
-/

open Cslib.Logic
@[inherit_doc] local infixr:36 " ∧ " => HasAnd.and

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[scoped grind =]
lemma Cslib.Logic.Modal.Proposition.and_def (φ₁ φ₂ : Proposition Atom) : φ₁.and φ₂ = (φ₁ ∧ φ₂) := rfl
