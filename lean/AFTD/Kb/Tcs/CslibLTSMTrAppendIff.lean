import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrSplit
import AFTD.Kb.Tcs.CslibLTSMTrComp
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.MTr.append_iff

Topic: computability   Node: 6ae2a5003dca

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.append_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multistep-transitions over `μs ++ μs'` are exactly multistep transitions over `μs` and `μs'` with a common end & start state (respectively).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Multistep-transitions over `μs ++ μs'` are exactly multistep transitions over `μs` and `μs'` with a common end & start state (respectively). -/
theorem Cslib.LTS.MTr.append_iff : lts.MTr s1 (μs ++ μs') s2 ↔ ∃ s, lts.MTr s1 μs s ∧ lts.MTr s μs' s2 := by
  refine ⟨MTr.split, ?_⟩
  intro ⟨_, h, h'⟩
  exact h.comp lts h'
