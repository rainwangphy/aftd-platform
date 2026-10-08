import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.ListFoldlMaxMem

/-!
# List.argMaxOn_mem

Topic: equilibria   Node: 532f74b7b00a

Provenance: formalization of a published result. Source: EconCSLib, `List.argMaxOn_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The chosen maximizer is a member of the list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- The chosen maximizer is a member of the list. -/
theorem List.argMaxOn_mem [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    argMaxOn f head tail ∈ head :: tail :=
  foldl_max_mem f tail head
