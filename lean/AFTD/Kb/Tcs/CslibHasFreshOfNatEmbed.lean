import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh
import AFTD.Kb.Tcs.CslibHasFreshToInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshOfInfinite

/-!
# Cslib.HasFresh.ofNatEmbed

Topic: algorithms   Node: 0d05fe186fc0

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasFresh.ofNatEmbed`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct a fresh element from an embedding of `ℕ` using `Nat.find`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open Finset in
/-- Construct a fresh element from an embedding of `ℕ` using `Nat.find`. -/
@[implicit_reducible]
def Cslib.HasFresh.ofNatEmbed {α : Type u} [DecidableEq α] (e : ℕ ↪ α) : HasFresh α where
  fresh s := e (Nat.find (p := fun n ↦ e n ∉ s) ⟨(s.preimage e e.2.injOn).max.succ,
    fun h ↦ not_lt_of_ge (le_max <| mem_preimage.2 h) (WithBot.lt_succ _)⟩)
  fresh_notMem s := Nat.find_spec (p := fun n ↦ e n ∉ s) _
