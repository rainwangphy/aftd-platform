import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstOneProposition

/-!
# Cslib.Logic.CLL.instTopProposition

Topic: proof_theory   Node: ca168a981ef7

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instTopProposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instTopProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.CLL.instTopProposition : Top (Proposition Atom) := ⟨.top⟩
