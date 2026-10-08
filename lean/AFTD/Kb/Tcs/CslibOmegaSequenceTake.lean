import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceHead
import AFTD.Kb.Tcs.CslibOmegaSequenceTail
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.take

Topic: algorithms   Node: 989edfb86e3d

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.take`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`take n s` returns a list of the `n` first elements of ω-sequence `s`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- `take n s` returns a list of the `n` first elements of ω-sequence `s` -/
def Cslib.ωSequence.take : ℕ → ωSequence α → List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))
