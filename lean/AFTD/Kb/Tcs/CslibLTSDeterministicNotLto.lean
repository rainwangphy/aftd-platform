import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSDeterministic

/-!
# Cslib.LTS.deterministic_not_lto

Topic: computability   Node: 001cd0931f4b

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.deterministic_not_lto`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other `μ`-derivative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- In a deterministic LTS, if a state has a `μ`-derivative, then it can have no other `μ`-derivative. -/
@[grind .]
theorem Cslib.LTS.deterministic_not_lto [h : lts.Deterministic] :
  ∀ s μ s' s'', s' ≠ s'' → lts.Tr s μ s' → ¬lts.Tr s μ s'' := by grind
