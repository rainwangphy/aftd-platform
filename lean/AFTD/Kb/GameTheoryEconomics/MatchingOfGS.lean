import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Matching

/-!
# Matching.ofGS

Topic: matching_markets   Node: 6099399e9534

Provenance: formalization of a published result. Source: EconCSLib, `Matching.ofGS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coerce a bijective `f : Fin n → Fin n` into `Matching (Fin n) (Fin n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
variable {n : ℕ} [NeZero n] in
/-- Coerce a bijective `f : Fin n → Fin n` into `Matching (Fin n) (Fin n)`. -/
noncomputable def Matching.ofGS (f : Fin n → Fin n) (hf : Function.Bijective f) :
    Matching (Fin n) (Fin n) where
  matchM := fun w => some (f w)
  matchW := fun m => some ((Equiv.ofBijective f hf).symm m)
  consistent := by
    intro m w; simp only [Option.some.injEq]
    rw [Equiv.symm_apply_eq]; exact eq_comm
