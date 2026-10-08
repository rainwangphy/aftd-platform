import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicModalProposition
import AFTD.Kb.LogicFoundations.CslibLogicHasDiamond
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasDiamondProposition
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasNotProposition
import AFTD.Kb.LogicFoundations.CslibLogicModalInstHasAndProposition

/-!
# Cslib.Logic.Modal.Proposition.diamond_def

Topic: proof_theory   Node: 240ad9803642

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.Modal.Proposition.diamond_def`. Lean proof by Fabrizio Montesi, Marianna Girlando, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/Modal/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.Modal.Proposition.diamond_def
-/

open Cslib.Logic
@[inherit_doc] local prefix:40 "◇" => HasDiamond.diamond

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[scoped grind =]
lemma Cslib.Logic.Modal.Proposition.diamond_def (φ : Proposition Atom) : φ.diamond = (◇φ) := rfl
