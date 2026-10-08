import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr
import AFTD.Kb.Tcs.CslibLTSExampleSuccessorLTS
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Example.successorLTS_transGen_lt

Topic: computability   Node: 0a627d5523b4

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Example.successorLTS_transGen_lt`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/ExampleTermination.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.Example.successorLTS_transGen_lt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem Cslib.LTS.Example.successorLTS_transGen_lt {n m : ℕ}
    (h : Relation.TransGen successorLTS.UnlabelledTr n m) : n < m := by
  apply Relation.transGen_minimal (r' := (· < ·)) at h
  · exact h
  · rintro n m ⟨μ, htr⟩
    simp only [successorLTS] at htr
    omega
