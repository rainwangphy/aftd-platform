import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh
import AFTD.Kb.Tcs.CslibHasFreshToInfinite

/-!
# Cslib.instHasFreshOfInfinite

Topic: algorithms   Node: 8bca58ad20f5

Provenance: formalization of a published result. Source: CSLib, `Cslib.instHasFreshOfInfinite`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

All infinite types have an associated (at least noncomputable) fresh function. This, in conjunction with `HasFresh.to_infinite`, characterizes `HasFresh`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- All infinite types have an associated (at least noncomputable) fresh function. This, in conjunction with `HasFresh.to_infinite`, characterizes `HasFresh`. -/
noncomputable instance Cslib.instHasFreshOfInfinite (α : Type u) [Infinite α] : HasFresh α where
  fresh s := Infinite.exists_notMem_finset s |>.choose
  fresh_notMem s := by grind
