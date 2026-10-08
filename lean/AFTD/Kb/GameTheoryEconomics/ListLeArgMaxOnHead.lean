import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOnGe

/-!
# List.le_argMaxOn_head

Topic: equilibria   Node: ea4ef7ad45ca

Provenance: formalization of a published result. Source: EconCSLib, `List.le_argMaxOn_head`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The argmax achieves at least the head's value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- The argmax achieves at least the head's value. -/
theorem List.le_argMaxOn_head [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    f head ≤ f (argMaxOn f head tail) :=
  argMaxOn_ge f head tail head List.mem_cons_self
