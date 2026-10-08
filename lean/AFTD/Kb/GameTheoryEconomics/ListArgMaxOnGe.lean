import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.ListFoldlMaxGe

/-!
# List.argMaxOn_ge

Topic: equilibria   Node: 67c421220ec5

Provenance: formalization of a published result. Source: EconCSLib, `List.argMaxOn_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Argmax.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Soundness: every element's `f`-image is `≤` the chosen maximizer's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X Y : Type*} in
/-- Soundness: every element's `f`-image is `≤` the chosen maximizer's. -/
theorem List.argMaxOn_ge [TotalPreorder Y] [DecidableLE Y] (f : X → Y)
    (head : X) (tail : List X) :
    ∀ x ∈ head :: tail, f x ≤ f (argMaxOn f head tail) :=
  foldl_max_ge f tail head
