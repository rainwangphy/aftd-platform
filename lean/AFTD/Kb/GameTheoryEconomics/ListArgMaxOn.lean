import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# List.argMaxOn

Topic: equilibria   Node: 798eb017110f

Provenance: formalization of a published result. Source: EconCSLib, `List.argMaxOn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A chosen maximizer of `f` on the non-empty list `head :: tail`, **computed** by a left fold that keeps the running maximizer (ties keep the later element). Computable: the fold needs only a decidable comparison `[DecidableLE Y]`; correctness (`argMaxOn_mem` / `argMaxOn_ge`) needs the total preorder.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- A chosen maximizer of `f` on the non-empty list `head :: tail`, **computed** by a left fold that keeps the running maximizer (ties keep the later element). Computable: the fold needs only a decidable comparison `[DecidableLE Y]`; correctness (`argMaxOn_mem` / `argMaxOn_ge`) needs the total preorder. -/
def List.argMaxOn [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) : X :=
  tail.foldl (fun a z => if f a ≤ f z then z else a) head
