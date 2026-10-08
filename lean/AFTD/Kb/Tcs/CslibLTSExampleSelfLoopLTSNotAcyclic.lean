import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSAcyclic
import AFTD.Kb.Tcs.CslibLTSExampleSelfLoopLTS
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.selfLoopLTS_not_acyclic

Topic: computability   Node: 5036edd8259b

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.selfLoopLTS_not_acyclic`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The self-loop LTS is not acyclic.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The self-loop LTS is not acyclic. -/
theorem Cslib.LTS.Example.selfLoopLTS_not_acyclic : ¬ selfLoopLTS.Acyclic :=
  fun h => h.acyclic.irrefl () (.single ⟨(), trivial⟩)
