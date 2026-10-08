import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition

/-!
# Cslib.Logic.CLL.instZeroProposition

Topic: proof_theory   Node: 53d45aa0418d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instZeroProposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instZeroProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.CLL.instZeroProposition : Zero (Proposition Atom) := ⟨.zero⟩
