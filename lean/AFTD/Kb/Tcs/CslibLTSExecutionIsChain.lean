import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSExecution
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr

/-!
# Cslib.LTS.Execution.isChain

Topic: computability   Node: 41ea6ab4077a

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Execution.isChain`. Lean proof by Fabrizio Montesi, Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Execution.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The states visited by an execution form a chain in the underlying unlabelled relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- The states visited by an execution form a chain in the underlying unlabelled relation. -/
theorem Cslib.LTS.Execution.isChain (hexec : lts.Execution s1 μs s2 ss) :
    ss.IsChain lts.UnlabelledTr := by
  grind [Execution, List.isChain_iff_getElem, UnlabelledTr]
