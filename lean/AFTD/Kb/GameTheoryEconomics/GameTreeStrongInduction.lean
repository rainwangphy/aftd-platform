import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeSizeMemTailLt
import AFTD.Kb.GameTheoryEconomics.GameTreeSizePos
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSize
import AFTD.Kb.GameTheoryEconomics.GameTreeSizeHeadLt
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren

/-!
# GameTree.strong_induction

Topic: equilibria   Node: bcf6e29205a4

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.strong_induction`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Strong induction**: to prove `motive g`, it suffices to handle `Leaf` and, for each `Node`, to prove the motive given the motive for every child (head or tail).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
/-- **Strong induction**: to prove `motive g`, it suffices to handle `Leaf` and, for each `Node`, to prove the motive given the motive for every child (head or tail). -/
theorem GameTree.strong_induction {motive : GameTree N U → Prop}
    (base : ∀ p, motive (Leaf p))
    (step : ∀ (m : N) (h : GameTree N U) (t : List (GameTree N U)),
              (∀ c ∈ h :: t, motive c) → motive (Node m h t))
    (g : GameTree N U) : motive g := by
  -- Well-founded recursion on `size`.
  suffices h : ∀ (n : ℕ) (g : GameTree N U), g.size ≤ n → motive g from
    h g.size g (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro g hg
      exact absurd hg (Nat.not_le_of_lt (size_pos g))
  | succ k ih =>
      intro g hg
      cases g with
      | Leaf p => exact base p
      | Node m h t =>
          apply step m h t
          intro c hmem
          apply ih c
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · have := size_head_lt m c t
            omega
          · have := size_mem_tail_lt m h t hmem'
            omega
