import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSAcyclic
import AFTD.Kb.Tcs.CslibLTSExampleSuccessorLTS
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSExampleSuccessorLTSTransGenLt

/-!
# Cslib.LTS.Example.successorLTS_acyclic

Topic: computability   Node: c2e5c40db111

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.successorLTS_acyclic`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.Example.successorLTS_acyclic
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.LTS.Example.successorLTS_acyclic : successorLTS.Acyclic where
  acyclic := ⟨fun n h => (Nat.lt_irrefl n) (successorLTS_transGen_lt h)⟩
