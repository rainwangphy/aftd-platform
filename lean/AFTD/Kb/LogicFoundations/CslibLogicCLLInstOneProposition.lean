import AFTD.Prelude
import AFTD.Kb.LogicFoundations.CslibLogicCLLProposition
import AFTD.Kb.LogicFoundations.CslibLogicCLLInstZeroProposition

/-!
# Cslib.Logic.CLL.instOneProposition

Topic: proof_theory   Node: 71482c3b1f07

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.instOneProposition`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Logic.CLL.instOneProposition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.Logic.CLL.instOneProposition : One (Proposition Atom) := ⟨.one⟩
